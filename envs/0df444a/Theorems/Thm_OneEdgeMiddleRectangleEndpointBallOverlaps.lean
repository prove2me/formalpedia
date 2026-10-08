-- Prove2me | Theorems.Thm_OneEdgeMiddleRectangleEndpointBallOverlaps
-- name    : OneEdgeMiddleRectangleEndpointBallOverlaps
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:41:05.179023+00:00
-- url     : https://prove2.me/theorems/b95fa13f-7bd2-4dc7-9e05-7995a8d97dca
-- title:
--   One Edge Middle Rectangle Endpoint Ball Overlaps
-- statement:
--   Let $A\subseteq\mathbb R^2$, let $a\ne b$, and let
--   $0<t_0<t_1<1$.  Suppose that the closed middle subsegment
--   $$
--     M=\{(1-t)a+t b: t_0\le t\le t_1\}
--   $$
--   has positive separation from $A$: for some $\delta>0$, every
--   $m\in M$ and $y\in A$ satisfy $\delta\le |m-y|$.  Let $U_a$ and
--   $U_b$ be open sets containing respectively the cut points
--   $(1-t_0)a+t_0b$ and $(1-t_1)a+t_1b$.  Then there are
--   $\varepsilon>0$ and three sets $R,L_+,L_-\subseteq\mathbb R^2$ such that
--   $R$ is nonempty and open, $L_+$ and $L_-$ are nonempty open connected
--   sets contained in $R$, both $L_+$ and $L_-$ are contained in
--   $(A\cup[a,b])^c$,
--   $$
--     R\setminus[a,b]\subseteq L_+\cup L_-,
--   $$
--   the middle axis
--   $$
--     \{(1-t)a+t b: t_0<t<t_1\}
--   $$
--   is contained in $R$, and each of $L_+$ and $L_-$ meets both $U_a$ and
--   $U_b$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeMiddleRectangleEndpointBallOverlaps`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeMiddleRectangleEndpointBallOverlaps.lean#L1-L484

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma OneEdgeMiddleRectangleEndpointBallOverlaps
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    (t0 t1 δ : ℝ)
    (Ua Ub : Set (EuclideanSpace ℝ (Fin 2)))
    (hab : a ≠ b)
    (ht0 : 0 < t0) (ht01 : t0 < t1) (ht1 : t1 < 1)
    (hδ : 0 < δ)
    (hsep :
      ∀ m, m ∈ AffineMap.lineMap a b '' Set.Icc t0 t1 →
        ∀ y, y ∈ A → δ ≤ dist m y)
    (hUa_open : IsOpen Ua)
    (hUb_open : IsOpen Ub)
    (hline_t0_Ua : AffineMap.lineMap a b t0 ∈ Ua)
    (hline_t1_Ub : AffineMap.lineMap a b t1 ∈ Ub) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ middleRect leftSide rightSide : Set (EuclideanSpace ℝ (Fin 2)),
        middleRect.Nonempty ∧ IsOpen middleRect ∧
        leftSide.Nonempty ∧ IsOpen leftSide ∧ IsConnected leftSide ∧
        rightSide.Nonempty ∧ IsOpen rightSide ∧ IsConnected rightSide ∧
        leftSide ⊆ middleRect ∧ rightSide ⊆ middleRect ∧
        leftSide ⊆ (A ∪ segment ℝ a b)ᶜ ∧
        rightSide ⊆ (A ∪ segment ℝ a b)ᶜ ∧
        middleRect \ segment ℝ a b ⊆ leftSide ∪ rightSide ∧
        AffineMap.lineMap a b '' Set.Ioo t0 t1 ⊆ middleRect ∧
        (leftSide ∩ Ua).Nonempty ∧ (rightSide ∩ Ua).Nonempty ∧
        (leftSide ∩ Ub).Nonempty ∧ (rightSide ∩ Ub).Nonempty := by sorry
