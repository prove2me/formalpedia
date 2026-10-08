-- Prove2me | Theorems.Thm_OneEdgeOldComponentBookkeeping
-- name    : OneEdgeOldComponentBookkeeping
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:41:15.083068+00:00
-- url     : https://prove2.me/theorems/3572a658-4198-44bc-9372-df385c0810a8
-- title:
--   One Edge Old Component Bookkeeping
-- statement:
--   Let $A\subseteq\mathbb R^2$, and let $\sigma=[a,b]$ be a
--   nondegenerate closed segment with $a,b\in A$.  Suppose that the relative
--   interior $\sigma^\circ$ is disjoint from $A$.  Then there is an old
--   complement component $C_\sigma$ of $A$ containing $\sigma^\circ$, this
--   old component is unique among complement components of $A$ containing
--   $\sigma^\circ$, and every complement component $C$ of $A$ with
--   $C\ne C_\sigma$ is disjoint from the closed segment $\sigma$ and remains a
--   complement component of $A\cup\sigma$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeOldComponentBookkeeping`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeOldComponentBookkeeping.lean#L1-L57

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma OneEdgeOldComponentBookkeeping
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ a b) A) :
    ∃ Csigma : Set (EuclideanSpace ℝ (Fin 2)),
      ComplementComponent A Csigma ∧
        openSegment ℝ a b ⊆ Csigma ∧
        (∀ D : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent A D → openSegment ℝ a b ⊆ D → D = Csigma) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent A C → C ≠ Csigma →
            Disjoint C (segment ℝ a b) ∧
              ComplementComponent (A ∪ segment ℝ a b) C := by sorry
