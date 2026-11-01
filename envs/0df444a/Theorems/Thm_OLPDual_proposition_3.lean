-- Prove2me | Theorems.Thm_OLPDual_proposition_3
-- name    : OLPDual.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:11.795322+00:00
-- url     : https://prove2.me/theorems/fdf368c1-791c-434f-b814-1b808759ac6b
-- title:
--   Proposition 3, p.12 — concentration of the sample sub-gradient
-- statement:
--   Let $u_1,\dots,u_n$ be i.i.d. from a law satisfying Assumption 1. For any $\epsilon>0$,
--
--   $$
--   \mathbb P\Bigl(\Bigl\|\frac1n\sum_{j=1}^n\phi(p^*,u_j)-\nabla f(p^*)\Bigr\|\le\epsilon\Bigr)\ge 1-2m\exp\Bigl(-\frac{n\epsilon^2}{2\bar a^2m}\Bigr).
--   $$
--
--   The bound does not depend on the distribution. It controls the first-order term of the identity (11).
--
--   Differences from the source:
--   - generalization: p* the optimal solution, 𝒫 ∈ Ξ → arbitrary pstar and a law satisfying Assumption 1 only; reason: the proof uses only the boundedness of φ; the printed statement is the special case
--   - generalization: Assumption 1 (d), n > m → n ≥ 1; reason: n > m ≥ 1 implies n ≥ 1 and the result does not use n > m
--   - encoding: u = (r, a) → u = (a, r); reason: order of the pair only; same law
--   - encoding: ℙ(event) → (sampleLaw law n).real of the event; reason: the event is measurable, so this is its probability
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Proposition 3, p.12; proof pp.33–34

import Mathlib
import Definitions.Def_OLPDual_Model
import Definitions.Def_OLPDual_EventE2

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Proposition 3**, Li–Ye, arXiv:1909.05499v5, p.12 (PDF 12):
`ℙ(‖(1/n) Σ_j φ(p*, u_j) − ∇f(p*)‖ ≤ ε) ≥ 1 − 2m exp(−nε²/(2ā²m))` for any `ε > 0`.
**Formalization Note** Only Assumption 1 is used, so `pstar` is an arbitrary point, and `n > m` is
relaxed to `n ≥ 1`. The event is measurable, so `Measure.real` is its probability. -/
theorem proposition_3 (Θ : Model) {m n : ℕ} (hn : 0 < n) (d : E m) (law : Measure (E m × ℝ))
    [IsProbabilityMeasure law] (hA1 : Assumption1 Θ d law) (pstar : E m) {ε : ℝ} (hε : 0 < ε) :
    1 - 2 * (m : ℝ) * Real.exp (-((n : ℝ) * ε ^ 2) / (2 * Θ.abar ^ 2 * (m : ℝ))) ≤
      (sampleLaw law n).real (EventE1 d law pstar ε n) := by sorry

end OLPDual
