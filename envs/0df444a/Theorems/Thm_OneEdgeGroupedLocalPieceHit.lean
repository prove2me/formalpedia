-- Prove2me | Theorems.Thm_OneEdgeGroupedLocalPieceHit
-- name    : OneEdgeGroupedLocalPieceHit
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T20:26:51.418403+00:00
-- url     : https://prove2.me/theorems/3cac99a1-d536-44b6-a9c6-08f7ba491cc9
-- title:
--   One Edge Grouped Local Piece Hit
-- statement:
--   Let $A\subseteq\mathbb R^2$, let $[a,b]$ be the new closed segment, and let
--   $C_\sigma\subseteq A^c$ be a polygonally path connected set containing the
--   open segment $(a,b)$.  Let $C$ be a complement component of
--   $A\cup[a,b]$ such that $C\subseteq C_\sigma$.  Let $U$ be an open
--   neighborhood of the closed segment $[a,b]$.
--
--   Suppose a finite retained raw local family $\{Q_i:i\in I\}$ covers every
--   point of $U\cap C_\sigma$ which is not on $[a,b]$.  Suppose also that each
--   retained raw piece $Q_i$ is contained in a grouped local piece $G_i$, and
--   that each $G_i$ belongs to a finite family $\mathcal G$.  Then $C$ meets
--   some member of $\mathcal G$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeGroupedLocalPieceHit`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeGroupedLocalPieceHit.lean#L1-L75

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected

open Classical
noncomputable section

lemma OneEdgeGroupedLocalPieceHit
    (A Csigma C localUnion : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    {ι : Type*}
    (rawPieces : Finset ι)
    (piece : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (groupedLocalPieces : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (groupedLocalPieceOf : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hC : ComplementComponent (A ∪ segment ℝ a b) C)
    (hC_subset_Csigma : C ⊆ Csigma)
    (hCsigma_subset_old_compl : Csigma ⊆ Aᶜ)
    (hCsigma_path : PolygonallyPathConnected Csigma)
    (hOpenSegment_Csigma : openSegment ℝ a b ⊆ Csigma)
    (hLocalUnion_open : IsOpen localUnion)
    (hSegment_subset_localUnion : segment ℝ a b ⊆ localUnion)
    (hraw_cover :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ localUnion ∩ Csigma →
          x ∉ segment ℝ a b →
            ∃ k ∈ rawPieces, x ∈ piece k)
    (hgroupedLocalPiece_mem :
      ∀ i, i ∈ rawPieces → groupedLocalPieceOf i ∈ groupedLocalPieces)
    (hrawPiece_subset_groupedLocalPiece :
      ∀ i, i ∈ rawPieces → piece i ⊆ groupedLocalPieceOf i) :
    ∃ G ∈ groupedLocalPieces, (C ∩ G).Nonempty := by sorry
