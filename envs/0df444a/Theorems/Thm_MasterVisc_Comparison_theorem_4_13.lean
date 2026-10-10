-- Prove2me | Theorems.Thm_MasterVisc_Comparison_theorem_4_13
-- name    : MasterVisc.Comparison.theorem_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:48:35.394788+00:00
-- url     : https://prove2.me/theorems/0e0ca4f3-6b15-4cee-af55-ecbeead6d919
-- title:
--   Theorem 4.13, p. 965 — under Assumption 3.1, if 𝒰̄_g, 𝒰̲_g ≠ ∅ and V̄ = V̲ =: V, then V₁ ≤ V ≤ V₂ and V is the unique viscosity solution
-- statement:
--   Let $G$ satisfy Assumption 3.1 and $g\in C^0(\mathcal P_2;\mathbb R)$. Assume $V_1$ and $V_2$ are a viscosity subsolution and a viscosity supersolution of the master equation (3.1) with
--   $$V_1(T,\cdot)\le g\le V_2(T,\cdot).$$
--   Assume further that $\underline{\mathcal U}_g$ and $\overline{\mathcal U}_g$ are not empty and that the Perron envelopes (4.17) agree:
--   $$\overline V=\underline V=:V.\qquad(4.19)$$
--   Then $V_1\le V\le V_2$ on $\Theta$, and $V$ is the unique viscosity solution of (3.1) with terminal condition $g$: $V(T,\cdot)=g$, $V$ is a viscosity solution, and every viscosity solution $W$ with $W(T,\cdot)=g$ equals $V$ on $\Theta$.
--
--   This is the comparison principle and well-posedness result for viscosity solutions of parabolic master equations on the Wasserstein space of path laws: whenever the piecewise classical sub- and supersolutions of §4.5 squeeze to a common value, that value is the only viscosity solution, and it lies between every viscosity subsolution and supersolution with the same terminal data.
--
--   **Formalization Note.** (4.19) is stated with a real-valued $V$, so both envelopes are finite on $\Theta$. Uniqueness is read with the terminal condition $g$ (without it uniqueness fails, e.g. by adding a constant when $G$ does not depend on $y$); $V(T,\cdot)=g$ is part of the conclusion and follows from (4.18).
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 4.13, p. 965, with (4.17)–(4.19), pp. 964–965

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
import Definitions.Def_MasterVisc_Comparison_Viscosity
import Definitions.Def_MasterVisc_Comparison_Perron
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MasterVisc.Comparison

/-- Theorem 4.13, p. 965: under Assumption 3.1 and `g ∈ C⁰(𝒫₂; ℝ)`, let `V₁`, `V₂` be a viscosity sub- and
supersolution of (3.1) with `V₁(T, ·) ≤ g ≤ V₂(T, ·)`; if `𝒰̲_g`, `𝒰̄_g` are nonempty and `V̄ = V̲ =: V`
(4.19), then `V₁ ≤ V ≤ V₂`, `V(T, ·) = g`, and `V` is the unique viscosity solution of (3.1) with terminal
condition `g`. -/
theorem theorem_4_13 {d : ℕ} {T : ℝ≥0} (L₀ : ℝ) (G : Gen d T) (hG : Assumption31 L₀ G)
    (g : Measure (Path d T) → ℝ) (hg : IsC0P2 g)
    (V₁ V₂ : ℝ≥0 → Measure (Path d T) → ℝ) (h₁ : IsViscSub G V₁) (h₂ : IsViscSuper G V₂)
    (hT : ∀ μ, IsP2 μ → V₁ T μ ≤ g μ ∧ g μ ≤ V₂ T μ)
    (hUu : ∃ (ψ : ℝ≥0 → Measure (Path d T) → ℝ) (D : PWData d T), InUunder G g ψ D)
    (hUb : ∃ (ψ : ℝ≥0 → Measure (Path d T) → ℝ) (D : PWData d T), InUbar G g ψ D)
    (V : ℝ≥0 → Measure (Path d T) → ℝ)
    (hV : ∀ t μ, t ≤ T → IsP2 μ → Vbar G g t μ = (V t μ : EReal) ∧ Vunder G g t μ = (V t μ : EReal)) :
    (∀ t μ, t ≤ T → IsP2 μ → V₁ t μ ≤ V t μ ∧ V t μ ≤ V₂ t μ) ∧
    (∀ μ, IsP2 μ → V T μ = g μ) ∧
    IsViscSol G V ∧
    ∀ W : ℝ≥0 → Measure (Path d T) → ℝ, IsViscSol G W → (∀ μ, IsP2 μ → W T μ = g μ) →
      ∀ t μ, t ≤ T → IsP2 μ → W t μ = V t μ := by sorry

end MasterVisc.Comparison
