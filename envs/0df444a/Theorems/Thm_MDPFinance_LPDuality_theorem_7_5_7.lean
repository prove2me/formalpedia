-- Prove2me | Theorems.Thm_MDPFinance_LPDuality_theorem_7_5_7
-- name    : MDPFinance.LPDuality.theorem_7_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:56:12.556426+00:00
-- url     : https://prove2.me/theorems/3d2cc088-cece-4f50-bf92-44f6a5f3aea0
-- title:
--   Theorem 7.5.7 — complementary slackness for the primal/dual pair
-- statement:
--   A feasible primal $v$ and dual $\mu$ are simultaneously optimal, with matching primal and dual
--   values, exactly when the primal constraint they are both tied to holds with *equality*
--   $\mu$-almost everywhere — the infinite-dimensional analogue of complementary slackness in
--   ordinary linear programming, and the key technical tool the strong duality theorem (the goal)
--   uses to certify optimality of the pair it exhibits.
--
--   **Moderation note.** The draft had no hypotheses at all (no bounding function, no contracting model, no setting for $IM$ and $p$), under which the integrals defining $Z_D$ and the values are default values; §7.5.2's standing setting is now stated as in Theorem 7.5.6.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 217, Theorem 7.5.7

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_LP

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

/-- Theorem 7.5.7 (Bäuerle–Rieder, p. 217, PDF 228). Let `v \in Z_P` and `\mu \in Z_D`. Then the
following statements are equivalent: (i) `v` and `\mu` are optimal and `val(P) = val(D)`. (ii)
`v(x) = Lv(x,a)` for `\mu`-almost all `(x,a) \in D`. Setting of §7.5.2 as in Theorem 7.5.6. -/
theorem theorem_7_5_7 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (hαb : M.β * αb < 1) (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤) (v : E → ℝ) (hv : v ∈ ZP M IMs)
    (μ : Measure (E × A)) (hμ : μ ∈ ZD M b IMs p) :
    (((∫ x, v x ∂p : ℝ) : EReal) = valP M IMs p ∧
        ((∫ xa, M.r xa ∂μ : ℝ) : EReal) = valD M b IMs p ∧ valP M IMs p = valD M b IMs p) ↔
      (∀ᵐ xa ∂μ, xa ∈ M.D → v xa.1 = M.r xa + M.β * ∫ x', v x' ∂(M.Q xa)) := by sorry

end MDPFinance.LPDuality
