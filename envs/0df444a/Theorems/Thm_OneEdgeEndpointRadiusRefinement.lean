-- Prove2me | Theorems.Thm_OneEdgeEndpointRadiusRefinement
-- name    : OneEdgeEndpointRadiusRefinement
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:33.958985+00:00
-- url     : https://prove2.me/theorems/2a4b2b11-39d0-4848-ae62-46e0b79ffdca
-- title:
--   One Edge Endpoint Radius Refinement
-- statement:
--   Let $a\ne b$ be the endpoints of a new edge in a finite straight-line
--   complex.  Suppose positive radii $\rho_a,\rho_b$ have already been chosen so
--   that $B(a,\rho_a)$ misses every old vertex other than $a$ and every old
--   edge not incident with $a$, and similarly $B(b,\rho_b)$ misses every old
--   vertex other than $b$ and every old edge not incident with $b$.  Then there
--   are smaller positive radii $r_a,r_b$ such that
--   $$
--     r_a\le \rho_a,\qquad r_b\le \rho_b,\qquad
--     r_a<\frac{|a-b|}{3},\qquad r_b<\frac{|a-b|}{3},\qquad
--     r_a+r_b<|a-b|,
--   $$
--   and the same vertex-avoidance and nonincident-edge-avoidance conclusions hold
--   with $r_a,r_b$ in place of $\rho_a,\rho_b$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeEndpointRadiusRefinement`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeEndpointRadiusRefinement.lean#L1-L84

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma OneEdgeEndpointRadiusRefinement
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    (ρa ρb : ℝ)
    (hab : a ≠ b)
    (hρa_pos : 0 < ρa) (hρb_pos : 0 < ρb)
    (hρa_vertices :
      ∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ a → v ∉ Metric.ball a ρa)
    (hρa_edges :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ a → e.2 ≠ a →
          Disjoint (Metric.ball a ρa) (segment ℝ e.1 e.2))
    (hρb_vertices :
      ∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ b → v ∉ Metric.ball b ρb)
    (hρb_edges :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ b → e.2 ≠ b →
          Disjoint (Metric.ball b ρb) (segment ℝ e.1 e.2)) :
    ∃ ra rb : ℝ,
      0 < ra ∧ 0 < rb ∧
        ra ≤ ρa ∧ rb ≤ ρb ∧
        ra < dist a b / 3 ∧ rb < dist a b / 3 ∧
        ra + rb < dist a b ∧
        (∀ v : EuclideanSpace ℝ (Fin 2),
          v ∈ V → v ≠ a → v ∉ Metric.ball a ra) ∧
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E → e.1 ≠ a → e.2 ≠ a →
            Disjoint (Metric.ball a ra) (segment ℝ e.1 e.2)) ∧
        (∀ v : EuclideanSpace ℝ (Fin 2),
          v ∈ V → v ≠ b → v ∉ Metric.ball b rb) ∧
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E → e.1 ≠ b → e.2 ≠ b →
            Disjoint (Metric.ball b rb) (segment ℝ e.1 e.2)) := by sorry
