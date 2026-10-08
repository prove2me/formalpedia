-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_property_3
-- name    : MatroidProphetKW.Single.property_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:36.518978+00:00
-- url     : https://prove2.me/theorems/617b6862-173e-4bb5-8771-0352d01a85d3
-- title:
--   §3.3 display — the thresholds (9) satisfy Property (3) with $\alpha = 2$
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set and $F_x$, $x \in \mathcal U$, probability distributions on $[0,\infty)$ with finite means. Run the algorithm of §3.3 (thresholds (9)) on any input sequence $\sigma$ with non-negative weights; let $A = A(\sigma)$ be the selected set, $A_{i-1} = A \cap \{x_1, \dots, x_{i-1}\}$, and $T_i(\sigma)$ the thresholds. For every set $V$ disjoint from $A$ with $A \cup V \in \mathcal I$,
--   $$\mathbb E\Big[\sum_{x_i \in V} w'(R(A_{i-1})) - w'(R(A_{i-1} \cup \{x_i\}))\Big] \;=\; 2 \sum_{x_i \in V} T_i(\sigma) \;\le\; \mathbb E\big[w'(R(A))\big],$$
--   the expectations over the ghost sample $w' \sim \bigotimes_x F_x$.
--
--   Together with the telescoping identity for Property (2), this shows that the algorithm of §3.3 has 2-balanced thresholds, so Proposition 1 applies with $\alpha = 2$.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 7, §3.3, display after "the property simply asserts that for every pair of disjoint sets A, V such that A ∪ V ∈ ℐ"

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Online
import Definitions.Def_MatroidProphetKW_Single_Algorithm

namespace MatroidProphetKW.Single

open MeasureTheory

/-- Property (3) with `α = 2` for the thresholds (9) (Kleinberg–Weinberg, arXiv:1201.4764v1, §3.3,
p. 7): on every input sequence, with `A = A(σ)` the set the algorithm of §3.3 selects and every `V`
disjoint from `A` with `A ∪ V ∈ ℐ`,
  `E[∑_{x_i ∈ V} w′(R(A_{i−1})) − w′(R(A_{i−1} ∪ {x_i}))] = 2 ∑_{x_i ∈ V} T_i(σ) ≤ E[w′(R(A))]`. -/
theorem property_3 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF0 : ∀ x, F x (Set.Iio 0) = 0) (hFi : ∀ x, Integrable id (F x))
    (l : List α) (hl : IsOrder l) (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (V : Finset α) (hdisj : Disjoint V (run M (kwThr M F) l w))
    (hAV : M.Indep (↑(run M (kwThr M F) l w ∪ V) : Set α)) :
    (∫ w', ∑ x ∈ V,
        (wt w' (Rset M ((run M (kwThr M F) l w).filter (fun y => l.idxOf y < l.idxOf x)) w')
          - wt w' (Rset M (insert x ((run M (kwThr M F) l w).filter
              (fun y => l.idxOf y < l.idxOf x))) w')) ∂(Measure.pi F)
        = 2 * ∑ x ∈ V, thrAt M (kwThr M F) l w x) ∧
      2 * ∑ x ∈ V, thrAt M (kwThr M F) l w x
        ≤ ∫ w', wt w' (Rset M (run M (kwThr M F) l w) w') ∂(Measure.pi F) := by sorry

end MatroidProphetKW.Single
