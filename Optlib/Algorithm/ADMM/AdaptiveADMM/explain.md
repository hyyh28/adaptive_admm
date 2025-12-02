# scheme

## 1) 头部与环境

```
import Optlib.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences

noncomputable section

open Set InnerProductSpace Topology Filter
```

- `import ...`：导入你要用到的库。`Optlib.Function.Proximal` 里通常有近端（prox）相关定义，`Mathlib.Topology.MetricSpace.Sequences` 提供度量空间与序列的拓扑工具。
- `noncomputable section`：告诉 Lean：这个区块里可能用到选择公理等“不可计算”的构造（比如最小值存在但没显式算法求）。数学上很常见。
- `open ...`：把一些命名空间打开，写法更简洁（比如直接写 `inner`、`univ` 等）。

------

## 2) 型别与结构（把空间设定清楚）

```
variable (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]
```

- 声明了三个空间 $E₁, E₂, F$。
- 每个空间都是**实内积空间**（`InnerProductSpace ℝ _`），并且是**有限维**（`FiniteDimensional ℝ _`），同时带有范数（由内积诱导）与阿贝尔群结构（向量加法）。
- 直觉：这是标准的有限维欧式空间设定，保证诸如伴随（adjoint）、子梯度、范数等都好用。

------

## 3) 原始优化问题（结构体 `OptProblem`）

```
class OptProblem [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ F] where
  f₁ : E₁ → ℝ
  f₂ : E₂ → ℝ
  A₁ : E₁ →L[ℝ] F
  A₂ : E₂ →L[ℝ] F
  b  : F
  lscf₁ : LowerSemicontinuous f₁
  lscf₂ : LowerSemicontinuous f₂
  cf₁ : ConvexOn ℝ univ f₁
  cf₂ : ConvexOn ℝ univ f₂
  nonempty : ∃ x₁ x₂, (A₁ x₁) + (A₂ x₂) - b = 0 ∧
              IsMinOn (fun (x₁,x₂) ↦ f₁ x₁ + f₂ x₂) univ (x₁,x₂)
```

- 这是一个**类型类**（本质上是一个带字段的结构体），封装了问题数据与基本假设。

- 字段含义：

  - `f₁ : E₁ → ℝ`，`f₂ : E₂ → ℝ`：目标函数的两部分（分别只依赖 $x₁$、$x₂$）。
  - `A₁ : E₁ →L[ℝ] F`，`A₂ : E₂ →L[ℝ] F`：从 $E₁,E₂$ 到约束空间 $F$ 的**连续线性算子**（`→L[ℝ]` 是 “连续线性映射” 的类型）。
  - `b : F`：约束右端向量。
  - `lscf₁/lscf₂`：两目标函数**下半连续**（常用于保证极小值存在、闭性等）。
  - `cf₁/cf₂`：两目标函数在全空间 `univ` 上**凸**。
  - `nonempty`：存在某个 $(x₁,x₂)$ 同时满足：
    1. 线性约束 $A₁x₁ + A₂x₂ - b = 0$（**可行**），
    2. 并且在全空间 `univ` 上使 $f₁(x₁) + f₂(x₂)$ 取得**极小**（`IsMinOn ... univ (x₁,x₂)`）。

- 直觉：这就把“标准分裂型凸优化问题”描述出来了：
  $$
  \min_{x₁,x₂}\ f₁(x₁)+f₂(x₂)\quad \text{s.t. } A₁x₁ + A₂x₂ = b.
  $$
  并附带一些常规的凸分析假设（凸、下半连续、存在极小点与可行解）。

> 小语法：这里把有限维条件又写了一遍（尽管上面整体已经假设过），属于“在这个类被使用时也需要这些实例可用”的保险式写法；冗余但无害。

------

## 4) 增广拉格朗日（AL）函数

```
def Augmented_Lagrangian_Function (opt : OptProblem E₁ E₂ F) (ρ : ℝ) :
    E₁ × E₂ × F → ℝ :=
  fun (x₁ , x₂ , y) =>
    (opt.f₁ x₁) + (opt.f₂ x₂) +
    inner y ((opt.A₁ x₁) + (opt.A₂ x₂) - opt.b) +
    ρ / 2 * ‖(opt.A₁ x₁) + (opt.A₂ x₂) - opt.b‖ ^ 2
```

- 输入：问题实例 `opt` 和罚参数 `ρ>0`。

- 输出：一个函数 $(x₁,x₂,y) \mapsto \mathbb{R}$，即
  $$
    \mathcal{L}_ρ(x₁,x₂,y)
    = f₁(x₁)+f₂(x₂) + \langle y,\; A₁x₁ + A₂x₂ - b\rangle
      + \frac{ρ}{2}\|A₁x₁ + A₂x₂ - b\|^2.
  $$

- `inner y (...)` 就是内积 $\langle y, \cdot \rangle$；`‖·‖` 是范数；`^ 2` 是平方。

- **关于“ρ 是固定的吗？”**：这个定义允许任何实数 `ρ` 作为参数。在“变罚参数 ADMM”里，你每一步会传入当前步的 `ρₖ k`，所以不是固定常数；而是**按步选择**。

------

## 5) 变罚参数 ADMM（定义迭代与假设）

```
class ADMM extends (OptProblem E₁ E₂ F) where
  x₁ : ℕ → E₁
  x₂ : ℕ → E₂
  y  : ℕ → F
  ρₖ : ℕ → ℝ                      -- 变罚参数序列
  τ  : ℝ
  hρₖ_pos : ∀ k, ρₖ k > 0         -- 每步的 ρₖ > 0
  ρmin : ℝ                        -- 统一下界
  hρmin_pos : ρmin > 0
  hρ_lb : ∀ k, ρmin ≤ ρₖ k        -- ρmin ≤ ρₖ
  htau : 0 < τ ∧ τ < (1 + √5)/2
```

- 这里 `ADMM` **继承** 了 `OptProblem`（Lean 会生成一个投影 `toOptProblem`）。所以 `ADMM` 里同时含有问题数据与迭代数据。
- `x₁, x₂, y : ℕ → ...`：ADMM 的迭代序列（第 `k` 次迭代对应 `k`）。
- `ρₖ : ℕ → ℝ`：**每步**的罚参数，可变（HWY/“He–Wang–Yuan”等文献常见设定）。
- `τ : ℝ`：对偶步长/松弛参数。
- `hρₖ_pos / ρmin / hρmin_pos / hρ_lb`：保障所有 `ρₖ(k)` 都**正**，而且有统一正下界 `ρmin`（避免过小）。
- `htau : 0 < τ ∧ τ < (1 + √5)/2`：`τ` 在 $ (0,\tfrac{1+\sqrt5}{2})$ 中（上界约 1.618，黄金分割），这是 HWY 型 ADMM 常用的收敛范围之一。

接着是三个**子问题/更新**条件：

### (a) $x₁$-子问题是极小点

```
  itex₁ :
    ∀ k, IsMinOn
      (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem (ρₖ k))
        (x₁ , x₂ k , y k))
      univ (x₁ (k+1))
```

- 固定第 `k` 步的 `(x₂^k, y^k)` 和罚参数 `ρₖ(k)`，把增广拉格朗日看作只关于 `x₁` 的函数。
- `IsMinOn ... univ (x₁ (k+1))` 表示：`x₁^{k+1}` 是这个函数在整个空间上的**全局极小点**。
- 直觉：这就是 ADMM 的 $x₁$-更新：$x₁^{k+1} \in \arg\min_{x₁}\ \mathcal{L}_{ρₖ(k)}(x₁, x₂^k, y^k)$。

### (b) $x₂$-子问题是极小点

```
  itex₂ :
    ∀ k, IsMinOn
      (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem (ρₖ k))
        (x₁ (k+1) , x₂ , y k))
      univ (x₂ (k+1))
```

- 同理，先用新 `x₁^{k+1}`，再把 AL 当作只关于 `x₂` 的函数，`x₂^{k+1}` 是其全局极小点。
- 直觉：$x₂^{k+1} \in \arg\min_{x₂}\ \mathcal{L}_{ρₖ(k)}(x₁^{k+1}, x₂, y^k)$。

### (c) 对偶变量（乘子）更新（HWY 变体）

```
  itey :
    ∀ k, y (k+1) = y k + (τ * ρₖ k) • ((A₁ $ x₁ (k+1)) + (A₂ $ x₂ (k+1)) - b)
```

- `•` 是实数标量乘。

- 这是**对偶上升**步：残差 $r^{k+1} := A₁x₁^{k+1}+A₂x₂^{k+1}-b$，
  $$
    y^{k+1} = y^k + τ\,ρₖ(k)\, r^{k+1}.
  $$

- 与“标准 ADMM”（步长常取 $τ=1$）相比，这里允许 $τ\neq 1$，并用可变 $ρₖ$。

> 语法提示：
>
> - `toOptProblem` 是 `extends` 自动生成的父结构字段名，表示把当前 `ADMM` 实例当作一个 `OptProblem` 来用。
> - `fun x ↦ ...` 是匿名函数；`$` 只是函数应用的低优先级写法，`A₁ $ x₁ (k+1)` 等价于 `A₁ (x₁ (k+1))`。

------

## 6) 凸 KKT 条件（以“性质”形式表达）

```
variable {E₁ E₂ F} in
class Convex_KKT (x₁ : E₁ )(x₂ : E₂)(y : F) (opt : OptProblem E₁ E₂ F) :Prop where
   subgrad₁ : -(ContinuousLinearMap.adjoint opt.A₁) y ∈ SubderivAt opt.f₁ x₁
   subgrad₂ : -(ContinuousLinearMap.adjoint opt.A₂) y ∈ SubderivAt opt.f₂ x₂
   eq       :  (opt.A₁ x₁) + (opt.A₂ x₂) = opt.b
```

- 这是一个“断言某三元组满足 KKT”的**命题类**（`Prop`）。
- `ContinuousLinearMap.adjoint opt.A₁`：$A₁$ 的**伴随算子** $A₁^*$（在实内积空间里就是转置）。
- `SubderivAt opt.f₁ x₁`：$f₁$ 在 $x₁$ 处的**次微分集合** $\partial f₁(x₁)$。
- 三条条件正是**凸问题的 KKT**：
  1. $-A₁^* y \in \partial f₁(x₁)$
  2. $-A₂^* y \in \partial f₂(x₂)$
  3. 原问题**可行**：$A₁x₁ + A₂x₂ = b$

直觉：这就把“$(x₁,x₂,y)$ 是最优原-对偶解”的必要充分条件（在凸情形下）形式化出来，后续常用来证明 ADMM 极限点满足 KKT。