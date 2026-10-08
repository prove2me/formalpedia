-- Prove2me | Theorems.Thm_MatroidProphetKW_Inter_eq_24
-- name    : MatroidProphetKW.Inter.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:19.442994+00:00
-- url     : https://prove2.me/theorems/d0034f40-f7bf-464e-9c60-bbc8d5a6f1ce
-- title:
--   (24) — $\mathbb E[\sum_{x_i\in R(A)}(w'(x_i) - T_i)^+] \ge \mathbb E[w'(R(A))] - \frac1\alpha \mathbb E[\sum_j w'(R_j(A))]$
-- statement:
--   Let $\mathcal I$ be the intersection of $p \ge 1$ matroids, let the weights have independent laws $F_x$ on $[0,\infty)$ with finite means, and let $w, w'$ be two independent draws. Let a threshold algorithm with non-negative thresholds satisfy property (14) of Definition 3 with parameter $\alpha$, and run it against an online weight-adaptive adversary on the weights $w$, with selected set $A$. Then
--   $$\mathbb E\Big[\sum_{x_i \in R(A)} (w'(x_i) - T_i)^+\Big] \ge \mathbb E\big[w'(R(A))\big] - \frac1\alpha\, \mathbb E\Big[\sum_j w'(R_j(A))\Big].$$
--
--   The paper obtains it by applying property (14) to the set $V = R(A)$, which is disjoint from $A$ and satisfies $A \cup R(A) \in \mathcal I$. It is the third of the three inequalities (22)–(24) from which Proposition 3 follows.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 17, Appendix A, (24)

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace MatroidProphetKW.Inter

/-- Inequality (24) (Appendix A, p. 17): for any threshold rule with non-negative thresholds
satisfying property (14) of Definition 3, against any online weight-adaptive adversary,
`E[∑_{x_i ∈ R(A)} (w′(x_i) − T_i)^+] ≥ E[w′(R(A))] − (1/α) E[∑_j w′(R_j(A))]`. -/
theorem eq_24
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hp : 0 < p) (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (a : ℝ) (rule : ThresholdRule α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (h14 : Balanced14 M F a rule) (adv : Adversary α) :
    (∫ w, ∫ w', MatroidProphetKW.Single.wt w' (Rint M (adaptiveSelected rule M adv w) w') ∂(law F) ∂(law F)) -
        (1 / a) * ∫ w, ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Rj M j (adaptiveSelected rule M adv w) w')
          ∂(law F) ∂(law F) ≤
      ∫ w, ∫ w', sumOn (revealOrder adv w) (Rint M (adaptiveSelected rule M adv w) w')
        (fun i => max (w' (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F) ∂(law F) := by sorry

end MatroidProphetKW.Inter
