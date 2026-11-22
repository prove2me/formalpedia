-- Prove2me | Theorems.Thm_Monotonicity_Theorem_definable_preimage
-- name    : Monotonicity_Theorem.definable_preimage
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:45:38.004141+00:00
-- url     : https://prove2.me/theorems/127758a4-8412-4cef-8295-85a0b6f9e54a
-- title:
--   Preimages of definable sets are definable
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, and let $f : I \to B$ be a definable function of one variable.
--
--   **Claim.** For every definable subset $T$ of the line, the preimage
--
--   $$f^{-1}(T) = \{y \in I : f(y) \in T\}$$
--
--   is a definable subset of the line.
--
--   Specialising $T$ gives the sets that carry the one-dimensional analysis of a definable function: taking $T = \{c\}$ produces the fibre $f^{-1}(c)$, and taking $T$ to be a half-line produces the superlevel set $\{y \in I : f(y) > c\}$ or the sublevel set $\{y \in I : f(y) < c\}$. Since o-minimality constrains definable subsets of the line to be finite unions of points and intervals, these preimages are exactly the sets to which the axiom can be applied when one studies where a definable function is constant, increasing, or decreasing.
--
--   **Formalization Note.** The preimage is expressed as the set of $y$ for which there is a proof that $y$ lies in the domain $I$ and the value of $f$ at $y$ lies in $T$; membership of $I$ is part of the statement because the function is formalized on the subtype of its domain.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 1, Section 2 (definable sets and functions: preimages of definable sets under definable maps are definable); used in Chapter 3, Section 1 for the Monotonicity Theorem.

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.definable_preimage {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    {T : Set (Power R 1)} (hT : M.S 1 T) :
    M.S 1 (fun y : Power R 1 => exists hy : I y, T (f.toFun (Subtype.mk y hy)).1) := by sorry
