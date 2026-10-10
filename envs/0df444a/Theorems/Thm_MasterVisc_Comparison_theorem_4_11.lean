-- Prove2me | Theorems.Thm_MasterVisc_Comparison_theorem_4_11
-- name    : MasterVisc.Comparison.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:20.956248+00:00
-- url     : https://prove2.me/theorems/c9ca2346-54f7-427e-99eb-cac9ad0e6969
-- title:
--   Theorem 4.11 (Partial comparison principle), p. 964 — V¹ ≤ V² when one of them is in C_b^{1,1,1}(Θ)
-- statement:
--   Let $G$ satisfy Assumption 3.1, let $V^1$ be a viscosity subsolution and $V^2$ a viscosity supersolution of the master equation (3.1). If $V^1(T,\cdot)\le V^2(T,\cdot)$ on $\mathcal P_2$ and either $V^1\in C_b^{1,1,1}(\Theta)$ or $V^2\in C_b^{1,1,1}(\Theta)$, then
--   $$V^1(t,\mu)\le V^2(t,\mu)\qquad\text{for all }(t,\mu)\in\Theta.$$
--
--   Partial comparison is the step from which the full comparison principle (Theorem 4.13) is obtained by the Perron-type envelopes of §4.5.
--
--   **Formalization Note.** As in Theorem 4.6, "$V\in C_b^{1,1,1}(\Theta)$" is replaced by the larger tube class (derivative data continuous on $\Theta$ and in $C_b^{1,1,1}([t_1,t_2]\times\mathcal P_L(t_1,\mu))$ for all $t_1<t_2\le T$, $L>0$, $\mu\in\mathcal P_2$) that agrees with $V$ on $\Theta$; this makes the statement at least as strong as printed. The sub- and supersolution may come with different constants $L$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 4.11, p. 964

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
import Definitions.Def_MasterVisc_Comparison_Viscosity
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MasterVisc.Comparison

/-- Theorem 4.11 (Partial comparison principle), p. 964: under Assumption 3.1, if `V¹` is a viscosity
subsolution, `V²` a viscosity supersolution, `V¹(T, ·) ≤ V²(T, ·)`, and one of them is in
`C_b^{1,1,1}(Θ)` (here: the tube class), then `V¹ ≤ V²` on `Θ`. -/
theorem theorem_4_11 {d : ℕ} {T : ℝ≥0} (L₀ : ℝ) (G : Gen d T) (hG : Assumption31 L₀ G)
    (V₁ V₂ : ℝ≥0 → Measure (Path d T) → ℝ) (h₁ : IsViscSub G V₁) (h₂ : IsViscSuper G V₂)
    (hT : ∀ μ, IsP2 μ → V₁ T μ ≤ V₂ T μ)
    (hreg : (∃ Φ : C111Data d T, IsC111bTubes Φ ∧
                ∀ t μ, t ≤ T → IsP2 μ → Φ.fn t μ = V₁ t μ) ∨
            (∃ Φ : C111Data d T, IsC111bTubes Φ ∧
                ∀ t μ, t ≤ T → IsP2 μ → Φ.fn t μ = V₂ t μ)) :
    ∀ t μ, t ≤ T → IsP2 μ → V₁ t μ ≤ V₂ t μ := by sorry

end MasterVisc.Comparison
