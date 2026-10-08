-- Prove2me | Theorems.Thm_MatroidProphetKW_Inter_eq_23
-- name    : MatroidProphetKW.Inter.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:31.612985+00:00
-- url     : https://prove2.me/theorems/54df18bb-ad4c-43d5-beef-9f84d847f8e6
-- title:
--   (23) — $\mathbb E[\sum_{x_i\in A}(w_i - T_i)^+] \ge \mathbb E[\sum_{x_i\in R(A)}(w'(x_i) - T_i)^+]$
-- statement:
--   Let $\mathcal I$ be the intersection of $p \ge 1$ matroids, let the weights have independent laws $F_x$ on $[0,\infty)$ with finite means, and let $w, w'$ be two independent draws. Run any threshold algorithm with non-negative thresholds against any online weight-adaptive adversary on the weights $w$; let $x_1,\dots,x_n$ be the order in which the elements are revealed, $T_i$ the threshold offered at step $i$, $w_i = w(x_i)$, and $A$ the selected set. Then
--   $$\mathbb E\Big[\sum_{x_i \in A} (w_i - T_i)^+\Big] \ge \mathbb E\Big[\sum_{x_i \in R(A)} (w'(x_i) - T_i)^+\Big],$$
--   where $(z)^+ = \max\{z, 0\}$ and, for $x_i \in R(A)$, $T_i$ is the threshold offered at the step in which $x_i$ was revealed.
--
--   This is the probabilistic step of the proof of Proposition 3: the algorithm collects every positive surplus $w_i - T_i$, and since $T_i$ and $x_i$ do not depend on $w(x_i)$, the surplus of $w$ and of the ghost sample $w'$ have the same expectation at every step.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 17, Appendix A, (23) ("deduced from the same observations as Equation (7)", p. 6)

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace MatroidProphetKW.Inter

/-- Inequality (23) (Appendix A, p. 17): for any threshold rule with non-negative thresholds,
played against any online weight-adaptive adversary,
`E[∑_{x_i ∈ A} (w_i − T_i)^+] ≥ E[∑_{x_i ∈ R(A)} (w′(x_i) − T_i)^+]`, where `w, w′` are
independent draws from the weight law and `T_i` is the threshold offered at the step at which
`x_i` was revealed. -/
theorem eq_23
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hp : 0 < p) (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (rule : ThresholdRule α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (adv : Adversary α) :
    ∫ w, ∫ w', sumOn (revealOrder adv w) (Rint M (adaptiveSelected rule M adv w) w')
        (fun i => max (w' (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F) ∂(law F) ≤
      ∫ w, sumOn (revealOrder adv w) (adaptiveSelected rule M adv w)
        (fun i => max (w (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F) := by sorry

end MatroidProphetKW.Inter
