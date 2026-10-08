-- Prove2me | Theorems.Thm_OneEdgeMiddleOpenSegmentNeighborhood
-- name    : OneEdgeMiddleOpenSegmentNeighborhood
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:39:31.667559+00:00
-- url     : https://prove2.me/theorems/0111fe32-b499-4ca6-9ff5-ef8ac0f5f17d
-- title:
--   One Edge Middle Open Segment Neighborhood
-- statement:
--   Let $a\ne b$ in $\mathbb R^2$, let $0<t_0<t_1<1$, and let
--   $R\subseteq\mathbb R^2$ be an open middle rectangle.  Suppose that
--   $$
--     \{(1-t)a+tb:t_0<t<t_1\}\subseteq R.
--   $$
--   Let $r_a,r_b$ be endpoint radii such that
--   $$
--     t_0|a-b|<r_a,\qquad (1-t_1)|a-b|<r_b,
--   $$
--   and suppose also that the two cut points
--   $(1-t_0)a+t_0b$ and $(1-t_1)a+t_1b$ lie respectively in
--   $B(a,r_a)$ and $B(b,r_b)$.  Then
--   $$
--     (B(a,r_a)\cup R)\cup B(b,r_b)
--   $$
--   is open and contains the open segment $(a,b)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeMiddleOpenSegmentNeighborhood`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeMiddleOpenSegmentNeighborhood.lean#L1-L65

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma OneEdgeMiddleOpenSegmentNeighborhood
    (a b : EuclideanSpace ℝ (Fin 2))
    (ra rb t0 t1 : ℝ)
    (middleRect : Set (EuclideanSpace ℝ (Fin 2)))
    (hab : a ≠ b)
    (ht0 : 0 < t0) (ht01 : t0 < t1) (ht1 : t1 < 1)
    (ht0_reaches_a : t0 * dist a b < ra)
    (ht1_reaches_b : (1 - t1) * dist a b < rb)
    (hline_t0_ball_a : AffineMap.lineMap a b t0 ∈ Metric.ball a ra)
    (hline_t1_ball_b : AffineMap.lineMap a b t1 ∈ Metric.ball b rb)
    (hmiddleRect_open : IsOpen middleRect)
    (haxis_subset :
      AffineMap.lineMap a b '' Set.Ioo t0 t1 ⊆ middleRect) :
    IsOpen ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) ∧
      openSegment ℝ a b ⊆
        ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) := by sorry
