-- Prove2me | Theorems.Thm_MatroidProphetKW_Inter_intersection_prophet
-- name    : MatroidProphetKW.Inter.intersection_prophet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:14.131802+00:00
-- url     : https://prove2.me/theorems/15a44f47-a275-4194-97cb-0b0eab97367c
-- title:
--   Prophet inequality for the intersection of $p$ matroids — the §4.2 algorithm with $\alpha = 2p$ earns $\mathbb E[w(A)] \ge \frac{1}{4p-2}\,\mathbb E[\mathrm{OPT}(w)]$
-- statement:
--   Let $\mathcal U$ be a finite ground set, let $\mathcal I = \mathcal I_1 \cap \dots \cap \mathcal I_p$ be the intersection of $p \ge 1$ matroids on $\mathcal U$, and let the weights $w(x)$, $x \in \mathcal U$, be independent with laws $F_x$ supported on $[0,\infty)$ with finite means. Run the summed-threshold algorithm of §4.2 with $\alpha = 2p$: at step $i$ it selects $x_i$ if and only if $A_{i-1} \cup \{x_i\} \in \mathcal I$ and
--   $$w(x_i) \ge T(A_{i-1}, i) = \sum_{j=1}^p \frac{1}{2p}\, \mathbb E_{w'}\big[w'(R_j(A_{i-1})) - w'(R_j(A_{i-1} \cup \{x_i\}))\big].$$
--   Then against every online weight-adaptive adversary the selected set $A$ satisfies
--   $$\mathbb E[w(A)] \ge \frac{1}{4p-2}\, \mathbb E\big[\mathrm{OPT}(w)\big].$$
--
--   For $p = 1$ this is the factor-2 matroid prophet inequality; for general $p$ it is the paper's guarantee for matroid intersections, stated in the abstract and the introduction.
--
--   **Formalization Note** The algorithm is the one defined in §4.2, built from the ghost-sample objects $B$, $R_j(\cdot)$; its thresholds are not free parameters. Adversaries are deterministic and measurable in the revealed weights (randomized adversaries are mixtures of these). Ties in the maximisers $B$ and $R_j(A)$ are broken by a fixed rule.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 9, Proposition 3; p. 10, §4.2 (α = 2p, guarantee 1/(4p−2)); abstract and p. 2

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace MatroidProphetKW.Inter

/-- Goal (Proposition 3 with `α = 2p` for the thresholds of §4.2, pp. 9–10; abstract and p. 2):
on the intersection of `p ≥ 1` matroids, against every online weight-adaptive adversary, the
summed-threshold algorithm with `α = 2p` selects a set `A` with
`E[w(A)] ≥ 1/(4p − 2) · E[OPT(w)]`. -/
theorem intersection_prophet
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hp : 0 < p) (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (adv : Adversary α) :
    1 / (4 * (p : ℝ) - 2) * ∫ w, OPT M w ∂(law F) ≤
      ∫ w, MatroidProphetKW.Single.wt w (adaptiveSelected (sumRule M F (2 * p)) M adv w) ∂(law F) := by sorry

end MatroidProphetKW.Inter
