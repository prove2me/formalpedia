-- Prove2me | Theorems.Thm_Monotonicity_Theorem_window_loci_definable
-- name    : Monotonicity_Theorem.window_loci_definable
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:28:25.217044+00:00
-- url     : https://prove2.me/theorems/566f5670-4c22-42da-878a-cf7391c0cbaf
-- title:
--   The window loci are definable
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, and let $f : I \to B$ be a definable function of one variable.
--
--   **Claim.** The three window loci of $f$ are definable, that is, each of
--
--   $$\{x : \exists\, u < x < v,\ f \text{ is constant on } I \cap (u,v)\},$$
--
--   $$\{x : \exists\, u < x < v,\ (u,v) \subseteq I \text{ and } f \text{ is strictly increasing on } (u,v)\},$$
--
--   $$\{x : \exists\, u < x < v,\ (u,v) \subseteq I \text{ and } f \text{ is strictly decreasing on } (u,v)\}$$
--
--   belongs to the collection $M.S\,1$ of definable subsets of the line.
--
--   Each locus is described by a first-order condition on $x$ built from the order relation, the domain $I$, and the graph of $f$, all of which are definable by hypothesis. The claim is therefore an instance of the closure of a structure under finite unions and intersections, complements, products, coordinate reindexing and projection. It is the step that makes o-minimality applicable to the local behaviour of $f$: once the loci are known to be definable, each is a finite union of points and intervals.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem); step of the proof of the finite-exceptional-set lemma of this mission.

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.window_loci_definable {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B) :
    M.S 1 (ConstWindowLocus f) /\ M.S 1 (IncWindowLocus f) /\ M.S 1 (DecWindowLocus f) := by sorry
