-- Prove2me | Theorems.Thm_OneEdgeEndpointSectorComplementPackage
-- name    : OneEdgeEndpointSectorComplementPackage
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T20:26:42.790972+00:00
-- url     : https://prove2.me/theorems/f7995c0e-9deb-4e39-ac3a-9f596d5ab7bb
-- title:
--   One Edge Endpoint Sector Complement Package
-- statement:
--   Let $V$ be a finite set of old vertices, let $E$ be a finite set of old
--   closed straight edges whose endpoints lie in $V$, and let
--   $$
--     A=V\cup\bigcup_{e\in E} e .
--   $$
--   Assume every old edge is nondegenerate and distinct old edge interiors are
--   disjoint.  Fix vertices $p,q\in V$ with $p\ne q$, and suppose the relative
--   interior of the new segment $[p,q]$ is disjoint from $A$.  Let $r>0$ be
--   a radius such that $B(p,r)$ contains no vertex of $V$ other than $p$ and
--   is disjoint from every old edge not incident with $p$.
--
--   Let $I_p$ be the finite set of old edges incident with $p$.  For
--   $i=\varnothing$, let $u_i=q-p$; for an incident old edge $e$, let
--   $u_e$ be the vector from $p$ to the other endpoint of $e$.  Then the
--   finite family of clockwise sectors in $B(p,r)$ determined by the positive
--   rays $p+\mathbb R_{>0}u_i$ may be chosen so that each sector is open and
--   connected, is contained in $B(p,r)$, is contained in
--   $(A\cup[p,q])^c$, and the sectors cover
--   $$
--     B(p,r)\cap (A\cup[p,q])^c .
--   $$
--   Moreover, every point of $A\cap B(p,r)$ different from $p$ lies on one of
--   the old incident positive radial germs from $p$, and every point of
--   $[p,q]$ different from $p$ lies on the new positive radial germ from
--   $p$ toward $q$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `OneEdgeEndpointSectorComplementPackage`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/OneEdgeEndpointSectorComplementPackage.lean#L1-L379

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Classical
noncomputable section

lemma OneEdgeEndpointSectorComplementPackage
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2)
    (hEdgeSource :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ∈ V)
    (hEdgeTarget :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.2 ∈ V)
    (hEdgeNondegenerate :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ e.2)
    (hEdgeOpenInteriorsDisjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → f ∈ E → e ≠ f →
          Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2))
    (hpV : p ∈ V) (hqV : q ∈ V)
    (hpq : p ≠ q)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ p q) A)
    (r : ℝ) (hr_pos : 0 < r)
    (hr_vertices :
      ∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ p → v ∉ Metric.ball p r)
    (hr_nonincident_edges :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ p → e.2 ≠ p →
          Disjoint (Metric.ball p r) (segment ℝ e.1 e.2)) :
    let Incident :=
      {e : {e // e ∈ E} // e.1.1 = p ∨ e.1.2 = p}
    let u : Option Incident → EuclideanSpace ℝ (Fin 2) :=
      fun i =>
        match i with
        | none => q - p
        | some e =>
            if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p
    ∃ clockwiseNext : Equiv.Perm (Option Incident),
      ∃ fullClockwiseTurn : ℝ,
      ∃ clockwiseTurn : Option Incident → Option Incident → ℝ,
      ∃ sector : Option Incident → Set (EuclideanSpace ℝ (Fin 2)),
        fullClockwiseTurn = 2 * Real.pi ∧
        0 < fullClockwiseTurn ∧
        (∀ i j : Option Incident, 0 < clockwiseTurn i j) ∧
        (∀ i j : Option Incident, clockwiseTurn i j ≤ fullClockwiseTurn) ∧
        (∀ i j : Option Incident, clockwiseTurn i j = fullClockwiseTurn ↔ j = i) ∧
        (∀ i j : Option Incident, j ≠ i →
          clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j) ∧
        (∀ i : Option Incident,
          clockwiseNext i = i ↔ ∀ j : Option Incident, j = i) ∧
        (∀ i : Option Incident,
          IsOpen (sector i) ∧
            IsConnected (sector i) ∧
            sector i ⊆ Metric.ball p r ∧
            sector i ⊆ (A ∪ segment ℝ p q)ᶜ) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ Metric.ball p r → x ∈ A → x ≠ p →
            ∃ i : Incident, ∃ t : ℝ, 0 < t ∧ x = p + t • u (some i)) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ segment ℝ p q → x ≠ p →
            ∃ t : ℝ, 0 < t ∧ x = p + t • u none) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ Metric.ball p r → x ∈ (A ∪ segment ℝ p q)ᶜ →
            ∃ i : Option Incident, x ∈ sector i) := by sorry
