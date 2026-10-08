-- Prove2me | Theorems.Thm_MatroidProphetKW_Inter_proposition_3
-- name    : MatroidProphetKW.Inter.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:26.809035+00:00
-- url     : https://prove2.me/theorems/f148aff9-1518-4d4d-9192-7bb38fcebbfa
-- title:
--   Proposition 3 — $\alpha$-balanced thresholds with $\alpha \ge 2$ give $\mathbb E[w(A)] \ge \frac{\alpha - p}{\alpha(\alpha-1)}\mathrm{OPT}$
-- statement:
--   Let $\mathcal I$ be the intersection of $p \ge 1$ matroids on a finite ground set, and let the weights $w(x)$ be independent with laws $F_x$ on $[0,\infty)$ with finite means. Let $\mathrm{OPT} = \mathbb E[\mathrm{OPT}(w)]$ be the expected weight of a maximum-weight feasible set. If a threshold algorithm with non-negative thresholds has $\alpha$-balanced thresholds (Definition 3) for some $\alpha \ge 2$, then against every online weight-adaptive adversary the set $A$ it selects satisfies
--   $$\mathbb E[w(A)] \ge \frac{\alpha - p}{\alpha(\alpha - 1)}\, \mathrm{OPT}. \qquad (15)$$
--
--   This reduces the prophet inequality for matroid intersections to the construction of balanced thresholds; §4.2 constructs them, and $\alpha = 2p$ gives the factor $\frac{1}{4p-2}$.
--
--   **Formalization Note** "Monotone algorithm" is formalized as a threshold rule (the paper's §2 characterization); the paper's thresholds lie in $\mathbb R_+ \cup \{\infty\}$, hence the hypothesis that the finite thresholds are non-negative. "Weight-adaptive adversaries" are the online weight-adaptive adversaries of §2.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 9, Proposition 3, (15); proof p. 17, Appendix A

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace MatroidProphetKW.Inter

/-- Proposition 3 (p. 9): if a monotone threshold algorithm has `α`-balanced thresholds for
`α ≥ 2`, then against every online weight-adaptive adversary, when `ℐ` is the intersection of
`p` matroids, `E[w(A)] ≥ (α − p)/(α(α − 1)) · OPT`, where `OPT = E[OPT(w)]`. -/
theorem proposition_3
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hp : 0 < p) (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (a : ℝ) (ha : 2 ≤ a) (rule : ThresholdRule α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (hbal : IsBalanced M F a rule) (adv : Adversary α) :
    (a - p) / (a * (a - 1)) * ∫ w, OPT M w ∂(law F) ≤
      ∫ w, MatroidProphetKW.Single.wt w (adaptiveSelected rule M adv w) ∂(law F) := by sorry

end MatroidProphetKW.Inter
