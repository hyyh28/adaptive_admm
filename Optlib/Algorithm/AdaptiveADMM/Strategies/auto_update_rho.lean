-- AUTO GENERATED Lean4 FILE
import Optlib.Algorithm.AdaptiveADMM.GeneralAdapter
noncomputable section

def update_fun (n : ℕ) (rho : ℝ) : ℝ :=
  match n with
  | 0 => rho * (2.0 : ℝ)
  | 1 => rho / (2.0 : ℝ)
  | 2 => rho * (2.0 : ℝ)
  | 3 => rho * (2.0 : ℝ)
  | 4 => rho / (2.0 : ℝ)
  | 5 => rho / (2.0 : ℝ)
  | _ => rho

def tau_seq (n : ℕ) : ℝ :=
  match n with
  | 0 => 1 / ((n : ℝ) + 2)^2
  | 1 => 1 / ((n : ℝ) + 2)^2
  | 2 => 1 / ((n : ℝ) + 2)^2
  | 3 => 1 / ((n : ℝ) + 2)^2
  | 4 => 1 / ((n : ℝ) + 2)^2
  | 5 => 1 / ((n : ℝ) + 2)^2
  | _ => 0

def adaptable_strategy_auto : AdaptableStrategy :=
{
  update_fun := update_fun,
  tau_seq := tau_seq,
  h_tau_nonneg := by
    intro n; dsimp [tau_seq];
    split <;> nlinarith,
  h_tau_summable := by
    admit,
  h_update_equiv := by
    intro n rho hρ_pos;
    dsimp [update_fun, tau_seq];
    split <;> try (left; ring)
    <;> try (right; left; field_simp; ring)
    <;> right; right; rfl
}

variable (fullrank₁ : Function.Injective base_admm_real.A₁)
variable (fullrank₂ : Function.Injective base_admm_real.A₂)

theorem auto_converges : ∃ x₁ x₂ y,
  Convex_KKT x₁ x₂ y base_admm_real.toOptProblem ∧
  Tendsto base_admm_real.x₁ atTop (𝓝 x₁) ∧
  Tendsto base_admm_real.x₂ atTop (𝓝 x₂) ∧
  Tendsto base_admm_real.y atTop (𝓝 y) := by
  apply GeneralAdapter.converges_from_adaptable_strategy base_admm_real base_admm_kkt_real adaptable_strategy_auto fullrank₁ fullrank₂