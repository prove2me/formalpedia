-- Prove2me | Theorems.Thm_Monotonicity_Theorem_definable_interval_dichotomy
-- name    : Monotonicity_Theorem.definable_interval_dichotomy
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:28:29.583412+00:00
-- url     : https://prove2.me/theorems/58675436-1ac9-4b2f-a126-b1d3f2ef994d
-- title:
--   A definable subset of the line has finitely many boundary points
-- statement:
--   Let $D$ be a dense linear order without endpoints and let $S$ be a subset of the line which is a finite union of points and open intervals — that is, a definable subset in the sense of the o-minimality axiom.
--
--   **Claim.** There is a finite set $F$ such that
--
--   $$u < v \ \text{ and } \ (u,v) \cap F = \emptyset \ \Longrightarrow\ (u,v) \subseteq S \ \text{ or } \ (u,v) \cap S = \emptyset.$$
--
--   In words: away from finitely many exceptional points, every open interval is either entirely inside $S$ or entirely outside it. The set $F$ plays the role of the boundary of $S$, and the statement is the form in which tameness of definable sets is used when a partition into finitely many pieces has to be produced: cutting at the points of $F$ separates the part of the line covered by $S$ from its complement.
--
--   This is a general fact about finite unions of points and intervals and involves no function and no o-minimal structure beyond the description of $S$.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem); step of the proof of the finite-exceptional-set lemma of this mission.

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.definable_interval_dichotomy {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {S : Set (Power R 1)} (hS : FiniteUnionOfPointsAndIntervals D S) :
    exists F : Set (Power R 1), IsFinite1 F /\
      forall u v : R, D.lt u v ->
        (forall x : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x -> Not (F x)) ->
        ((openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset S \/
          forall x : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x -> Not (S x)) := by sorry
