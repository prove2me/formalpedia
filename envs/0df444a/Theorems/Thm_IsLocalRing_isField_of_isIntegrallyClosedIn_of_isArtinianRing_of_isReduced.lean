-- Prove2me | Theorems.Thm_IsLocalRing_isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced
-- name    : IsLocalRing.isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/7b7efa25-5a41-5127-ab54-c47598d01596
-- title:
--   Reduced Artinian algebras integrally closed over a local ring
-- statement:
--   Let $B$ be a commutative ring that is local, and let $F$ be a nontrivial commutative ring equipped with a $B$-algebra structure, assumed to be Artinian as a ring and reduced. Assume further that $B$ is integrally closed in $F$, in the sense of the Mathlib predicate `IsIntegrallyClosedIn B F`: every element of $F$ that is integral over $B$ already lies in the image of the structure map $B \to F$ (no injectivity of that map, and no domain or fraction-field hypothesis on $B$ or $F$, is assumed). The conclusion is that $F$ is a field, i.e. $F$ satisfies Mathlib's `IsField`: it has two distinct elements $0 \ne 1$, its multiplication is commutative, and every nonzero element of $F$ has a multiplicative inverse. Note that the conclusion is about $F$ alone; nothing is asserted about $B$ beyond the hypotheses.
--
--   A lemma of commutative algebra: over a local base in which it is integrally closed, a reduced Artinian algebra cannot split, hence is a single residue field rather than a finite product of fields. It is used in the proof of [`IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing`](thm.html#IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing), where the total ring of fractions of a local ring must be shown to be a field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced
    {B F : Type*} [CommRing B] [IsLocalRing B] [CommRing F] [Nontrivial F] [Algebra B F]
    [IsArtinianRing F] [IsReduced F] (h : IsIntegrallyClosedIn B F) :
    IsField F := by sorry
