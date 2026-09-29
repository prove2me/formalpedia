-- Prove2me | Theorems.Thm_IsGaloisGroup_finrank_eq_index_of_isFractionRing_fixedPoints
-- name    : IsGaloisGroup.finrank_eq_index_of_isFractionRing_fixedPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/47dd56cc-6ed2-5734-b918-24a5549bb820
-- title:
--   Degree of the fraction field of H-invariants equals (G:H)
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ a domain, let $B$ be an $A$-algebra whose structure map is injective (`FaithfulSMul A B`), and let $G$ be a finite group acting on $B$ by ring automorphisms in such a way that the action realises $G$ as a Galois group of $B$ over $A$ in Mathlib's sense (`IsGaloisGroup G A B`): the action is faithful, it commutes with the $A$-algebra structure, and every $G$-invariant element of $B$ lies in the image of $A$. Let $H$ be a subgroup of $G$, and write $B^{H}$ for `FixedPoints.subalgebra A B H`, the $A$-subalgebra of elements of $B$ fixed by every element of $H$. Let $K$ and $E$ be fields, $K$ a fraction field of $A$ and $E$ a fraction field of $B^{H}$, equipped with an $A$-algebra structure on $E$ and a $K$-algebra structure on $E$ compatible with these, i.e. $A \to K \to E$ and $A \to B^{H} \to E$ are scalar towers. Then the $K$-vector space dimension of $E$ equals the index of $H$ in $G$: $\operatorname{finrank}_K E = (G:H)$.
--
--   This is the fixed-field theorem in the form needed for invariants of a finite group acting on a domain: passing to fraction fields, the invariants of a subgroup have degree equal to its index. It is used in the construction of a subalgebra attached to an inertia subgroup, where it supplies the degree count ([`IsGaloisGroup.exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq`](thm.html#IsGaloisGroup.exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGaloisGroup_finrank_eq_index_of_isFractionRing_fixedPoints.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsGaloisGroup.finrank_eq_index_of_isFractionRing_fixedPoints
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (H : Subgroup G)
    (K E : Type*) [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra (FixedPoints.subalgebra A B H) E] [IsFractionRing (FixedPoints.subalgebra A B H) E]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [IsScalarTower A (FixedPoints.subalgebra A B H) E] :
    Module.finrank K E = H.index := by sorry
