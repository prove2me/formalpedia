-- Prove2me | Theorems.Thm_OneEdgeEndpointGermPositiveRayDistinct
-- name    : OneEdgeEndpointGermPositiveRayDistinct
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:35.661956+00:00
-- url     : https://prove2.me/theorems/cd914427-cb75-450c-af59-1e6a392cb423
-- title:
--   One Edge Endpoint Germ Positive Ray Distinct
-- statement:
--   Let $A\subseteq\mathbb R^2$ be written as
--   $$
--     A=V\cup\bigcup_{e\in E} e
--   $$
--   for a finite vertex set $V$ and a finite set $E$ of nondegenerate closed
--   straight edges.  Assume distinct old edge relative interiors are disjoint.
--   Let $[p,q]$ be a nondegenerate new segment whose relative interior is
--   disjoint from $A$.
--
--   At the endpoint $p$, index the endpoint germs by one new germ in the
--   direction $q-p$, together with one old germ for each old edge of $E$
--   incident with $p$, directed from $p$ toward its other endpoint.  Then all
--   these germ vectors are nonzero, and no two distinct indexed germs determine
--   the same positive ray from $p$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeEndpointGermPositiveRayDistinct`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeEndpointGermPositiveRayDistinct.lean#L1-L271

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma OneEdgeEndpointGermPositiveRayDistinct
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2)
    (hEdgeNondegenerate :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ e.2)
    (hEdgeOpenInteriorsDisjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → f ∈ E → e ≠ f →
          Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2))
    (hpq : p ≠ q)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ p q) A) :
    let Incident :=
      {e : {e // e ∈ E} // e.1.1 = p ∨ e.1.2 = p}
    let u : Option Incident → EuclideanSpace ℝ (Fin 2) :=
      fun i =>
        match i with
        | none => q - p
        | some e =>
            if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p
    (∀ i : Option Incident, u i ≠ 0) ∧
      (∀ {i j : Option Incident},
        (∃ t : ℝ, 0 < t ∧ u j = t • u i) → i = j) := by sorry
