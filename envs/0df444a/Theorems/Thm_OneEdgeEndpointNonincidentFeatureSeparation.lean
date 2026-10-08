-- Prove2me | Theorems.Thm_OneEdgeEndpointNonincidentFeatureSeparation
-- name    : OneEdgeEndpointNonincidentFeatureSeparation
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:28.427325+00:00
-- url     : https://prove2.me/theorems/c4f88851-fa1b-4c11-9901-4faa33958333
-- title:
--   One Edge Endpoint Nonincident Feature Separation
-- statement:
--   Let $V$ be a finite vertex set and $E$ a finite family of old straight
--   edges in the plane.  Fix a vertex $p\in V$.  Assume that no vertex of $V$
--   lies in the relative interior of any old edge of $E$.  Then there is a
--   radius $\rho>0$ such that the open ball $B(p,\rho)$ contains no vertex of
--   $V$ other than $p$, and is disjoint from every old edge of $E$ that is
--   not incident with $p$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeEndpointNonincidentFeatureSeparation`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeEndpointNonincidentFeatureSeparation.lean#L1-L119

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.Order.Compact

open Classical
noncomputable section

lemma OneEdgeEndpointNonincidentFeatureSeparation
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2))
    (hNoVertexInEdgeInterior :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E →
          ∀ v : EuclideanSpace ℝ (Fin 2),
            v ∈ V → v ∉ openSegment ℝ e.1 e.2)
    (hpV : p ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ p → v ∉ Metric.ball p ρ) ∧
      (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ p → e.2 ≠ p →
          Disjoint (Metric.ball p ρ) (segment ℝ e.1 e.2)) := by sorry
