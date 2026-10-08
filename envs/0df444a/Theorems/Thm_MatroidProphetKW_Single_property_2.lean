-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_property_2
-- name    : MatroidProphetKW.Single.property_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:47.621218+00:00
-- url     : https://prove2.me/theorems/9d877163-fb7f-43e0-9b4e-6a9788f8f060
-- title:
--   §3.3 telescoping display — the thresholds (9) satisfy $\sum_{x_i\in A} T_i = \tfrac12\,\mathbb E[w'(C(A))]$
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set and $F_x$, $x \in \mathcal U$, probability distributions on $[0,\infty)$ with finite means. Run the algorithm of §3.3 (thresholds (9)) on any input sequence $\sigma$ with non-negative weights, and let $A = A(\sigma)$ be the selected set and $T_i = T_i(\sigma)$ the thresholds. Then
--   $$\sum_{x_i \in A} T_i \;=\; \tfrac12\, \mathbb E\big[w'(C(A))\big],$$
--   the expectation over the ghost sample $w' \sim \bigotimes_x F_x$.
--
--   In particular the thresholds (9) satisfy Property (2) of Definition 1 with $\alpha = 2$, with equality. The identity is a telescoping sum over the successive selections $A_0 = \emptyset \subseteq A_1 \subseteq \dots \subseteq A_n = A$.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 7, §3.3, display after "Property (2) in the definition of α-balanced thresholds follows from a telescoping sum."

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Online
import Definitions.Def_MatroidProphetKW_Single_Algorithm

namespace MatroidProphetKW.Single

open MeasureTheory

/-- Property (2) for the thresholds (9), by the telescoping sum of §3.3 (Kleinberg–Weinberg,
arXiv:1201.4764v1, p. 7): on every input sequence, with `A = A(σ)` the set the algorithm of §3.3
selects,
  `∑_{x_i ∈ A} T_i = ½ · E[w′(C(A))]`. -/
theorem property_2 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF0 : ∀ x, F x (Set.Iio 0) = 0) (hFi : ∀ x, Integrable id (F x))
    (l : List α) (hl : IsOrder l) (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ∑ x ∈ run M (kwThr M F) l w, thrAt M (kwThr M F) l w x
      = (1 / 2) * ∫ w', wt w' (Cset M (run M (kwThr M F) l w) w') ∂(Measure.pi F) := by sorry

end MatroidProphetKW.Single
