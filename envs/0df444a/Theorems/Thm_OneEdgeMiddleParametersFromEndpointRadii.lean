-- Prove2me | Theorems.Thm_OneEdgeMiddleParametersFromEndpointRadii
-- name    : OneEdgeMiddleParametersFromEndpointRadii
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:41:03.140362+00:00
-- url     : https://prove2.me/theorems/6d6d5e9d-5292-47a4-9bac-e4a051a9a4f0
-- title:
--   One Edge Middle Parameters From Endpoint Radii
-- statement:
--   Let $a\ne b$ and let $r_a,r_b>0$ be endpoint radii satisfying
--   $$
--     r_a+r_b<|a-b|.
--   $$
--   Then there are parameters $0<t_0<t_1<1$ such that the closed parameter
--   interval $[t_0,t_1]$ lies in the relative interior of $[a,b]$, the initial
--   cut point $(1-t_0)a+t_0b$ lies in $B(a,r_a)$, the terminal cut point
--   $(1-t_1)a+t_1b$ lies in $B(b,r_b)$, and
--   $$
--     t_0|a-b|<r_a,\qquad (1-t_1)|a-b|<r_b .
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeMiddleParametersFromEndpointRadii`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeMiddleParametersFromEndpointRadii.lean#L1-L71

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

lemma OneEdgeMiddleParametersFromEndpointRadii
    (a b : EuclideanSpace ℝ (Fin 2))
    (ra rb : ℝ)
    (hab : a ≠ b)
    (hra_pos : 0 < ra) (hrb_pos : 0 < rb)
    (hradii_sum_lt : ra + rb < dist a b) :
    ∃ t0 t1 : ℝ,
      0 < t0 ∧ t0 < t1 ∧ t1 < 1 ∧
        t0 * dist a b < ra ∧
        (1 - t1) * dist a b < rb ∧
        AffineMap.lineMap a b t0 ∈ Metric.ball a ra ∧
        AffineMap.lineMap a b t1 ∈ Metric.ball b rb ∧
        (∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ∈ Set.Ioo (0 : ℝ) 1) := by sorry
