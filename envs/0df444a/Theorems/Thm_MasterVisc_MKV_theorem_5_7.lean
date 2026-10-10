-- Prove2me | Theorems.Thm_MasterVisc_MKV_theorem_5_7
-- name    : MasterVisc.MKV.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:35:14.676818+00:00
-- url     : https://prove2.me/theorems/2545f921-7ce7-4587-bba5-5426cab996db
-- title:
--   Theorem 5.7, p. 971 — regularity of V: |V(t₁, μ) − V(t₂, ν)| ≤ Cρ(𝒲₂((t₁, μ), (t₂, ν))) + C[1 + 𝒲₂(μ_{[0,t₁]}, δ_{0})][t₂ − t₁]
-- statement:
--   Let Assumption 5.1 hold. Then there exist a modulus of continuity function $\rho$ and a constant $C$ such that for all $0\le t_1\le t_2\le T$ and $\mu,\nu\in\mathcal P_2$, the values $V(t_1,\mu)$, $V(t_2,\nu)$ are finite and
--   $$|V(t_1,\mu)-V(t_2,\nu)|\le C\rho\big(\mathcal W_2((t_1,\mu),(t_2,\nu))\big)+C\big[1+\mathcal W_2(\mu_{[0,t_1]},\delta_{\{0\}})\big][t_2-t_1].\tag{5.4}$$
--   If in addition $f$ is bounded, then $V$ is uniformly continuous in $(t,\mu)$ for the pseudometric (2.5).
--
--   In particular $V\in C^0(\Theta)$, which is the regularity Definition 4.4 requires of a viscosity solution.
--
--   **Formalization Note.** The constant $C$ of (5.4) is a constant of the conclusion, distinct from the constant $C$ of Assumption 5.1(iii); it is existential, chosen with $\rho$ before $t_1,t_2,\mu,\nu$. $\delta_{\{0\}}$ is the Dirac mass at the zero path. Finiteness of $V$ is part of the claim because (5.4) subtracts its values. Uniform continuity is stated for a real-valued function equal to $V$ on $\Theta$. $A$ is a nonempty Polish space with its Borel $\sigma$-algebra.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 5.7, (5.4), p. 971

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting
import Definitions.Def_MasterVisc_MKV_Control

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

/-- Theorem 5.7, p. 971: under Assumption 5.1 there are a modulus `ρ` and a constant `C` with
`|V(t₁, μ) − V(t₂, ν)| ≤ Cρ(𝒲₂((t₁, μ), (t₂, ν))) + C[1 + 𝒲₂(μ_{[0,t₁]}, δ_{0})][t₂ − t₁]` (5.4);
if moreover `f` is bounded, `V` is uniformly continuous in `(t, μ)`. -/
theorem theorem_5_7 {d : ℕ} {T : ℝ≥0}
    {A : Type} [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
    [Nonempty A]
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → EthierKurtz.SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (C₀ L₀ C : ℝ) (ρ₀ : ℝ → ℝ) (hρ₀ : IsModulus ρ₀)
    (hA : Assumption51 C₀ L₀ ρ₀ C b σ f g) :
    (∃ (ρ : ℝ → ℝ) (C' : ℝ), IsModulus ρ ∧
      ∀ (t₁ t₂ : ℝ≥0) (μ ν : Measure (MasterVisc.Comparison.Path d T)), t₁ ≤ t₂ → t₂ ≤ T → MasterVisc.Comparison.IsP2 μ → MasterVisc.Comparison.IsP2 ν →
        ∃ x y : ℝ, Vval b σ f g t₁ μ = x ∧ Vval b σ f g t₂ ν = y ∧
          |x - y| ≤ C' * ρ (MasterVisc.Comparison.W2Θ t₁ μ t₂ ν) +
            C' * (1 + W2 (MasterVisc.Comparison.restr t₁ μ) (Measure.dirac 0)) * ((t₂ : ℝ) - t₁)) ∧
    ((∃ M : ℝ, ∀ t ω μ a, t ≤ T → MasterVisc.Comparison.IsP2 μ → |f t ω μ a| ≤ M) →
      ∃ v : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ,
        (∀ t μ, t ≤ T → MasterVisc.Comparison.IsP2 μ → Vval b σ f g t μ = v t μ) ∧
        ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (t₁ t₂ : ℝ≥0) (μ ν : Measure (MasterVisc.Comparison.Path d T)),
          t₁ ≤ T → t₂ ≤ T → MasterVisc.Comparison.IsP2 μ → MasterVisc.Comparison.IsP2 ν → MasterVisc.Comparison.W2Θ t₁ μ t₂ ν < δ →
            |v t₁ μ - v t₂ ν| < ε) := by sorry

end MasterVisc.MKV
