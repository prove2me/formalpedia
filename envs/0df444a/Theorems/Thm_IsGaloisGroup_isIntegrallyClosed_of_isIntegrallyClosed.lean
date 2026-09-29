-- Prove2me | Theorems.Thm_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed
-- name    : IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/9c2378a5-6801-53df-b860-16231618c8ca
-- title:
--   Invariant subrings of integrally closed domains are integrally closed
-- statement:
--   Let $G$ be a group and let $A$ and $B$ be commutative rings that are integral domains, with $B$ an $A$-algebra. Assume the $A$-action on $B$ is faithful (`FaithfulSMul A B`, so that `algebraMap A B` is injective), and that $G$ acts on $B$ by ring automorphisms (`MulSemiringAction G B`) in such a way that `IsGaloisGroup G A B` holds; the content of this class used here is that the $G$-action is compatible with the $A$-action, so that the image of $A$ in $B$ is fixed pointwise, and that conversely every element of $B$ fixed by all of $G$ lies in the image of `algebraMap A B`. Assume finally that $B$ is integrally closed in its fraction field. The conclusion is that $A$ is integrally closed in its fraction field. No finiteness hypothesis on $G$, and no further hypothesis on the extension $A \to B$, is imposed.
--
--   This is the classical statement that normality descends from a domain to its subring of invariants under a group of ring automorphisms. It is used in the project when invariant subrings of explicitly constructed rings are shown to be normal, for instance in the verification of properties of invariants of rigid charts on modular curves and in the criterion for finite presentation and smoothness of invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed
    (G : Type*) [Group G] {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B] [IsGaloisGroup G A B]
    [IsIntegrallyClosed B] : IsIntegrallyClosed A := by sorry
