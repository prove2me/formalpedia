-- Prove2me | Theorems.Thm_MatroidProphetKW_Inter_eq_13
-- name    : MatroidProphetKW.Inter.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:01.69538+00:00
-- url     : https://prove2.me/theorems/2529ced1-c4b1-498e-b20d-19c31fa9da10
-- title:
--   (13) for the thresholds of §4.2 — $\sum_{x_i\in A} T_i = \frac1\alpha \mathbb E[\sum_j w'(C_j(A))]$
-- statement:
--   Run the summed-threshold algorithm of §4.2 with parameter $\alpha$ on an input sequence $\sigma$ (an order $x_1,\dots,x_n$ of the ground set, each element once, and any weights), and let $A = A(\sigma)$ be the selected set. Then
--   $$\sum_{x_i \in A} T_i(\sigma) = \frac1\alpha\, \mathbb E\Big[\sum_j w'(C_j(A))\Big],$$
--   the expectation being over the ghost sample $w'$.
--
--   In particular the algorithm satisfies inequality (13) of Definition 3 with equality. The paper says "the proof of Equation (13) follows exactly the proof of Equation (2)", a telescoping sum over the accepted elements that uses $C_j(\emptyset) = \emptyset$.
--
--   **Formalization Note** The weight law is assumed supported on $[0,\infty)$ with finite means, so that the expectations are finite.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 9, Definition 3, (13); p. 10, §4.2 ("The proof of Equation (13) follows exactly the proof of Equation (2).")

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace MatroidProphetKW.Inter

/-- Equation (13) for the thresholds of §4.2 (p. 10, "The proof of Equation (13) follows exactly
the proof of Equation (2)"), in the telescoped form with equality: for every input order `xs`
and weight vector `w`, with `A = A(σ)` the set the §4.2 algorithm selects,
`∑_{x_i ∈ A} T_i(σ) = (1/α) E[∑_j w′(C_j(A))]`. -/
theorem eq_13
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (a : ℝ) (xs : List α) (hnd : xs.Nodup) (hall : ∀ x, x ∈ xs) (w : α → ℝ) :
    sumOn xs (selected (sumRule M F a) M xs w) (thrAt (sumRule M F a) M xs w) =
      (1 / a) * ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Cj M j (selected (sumRule M F a) M xs w) w') ∂(law F) := by sorry

end MatroidProphetKW.Inter
