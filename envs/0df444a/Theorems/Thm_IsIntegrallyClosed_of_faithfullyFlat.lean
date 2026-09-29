-- Prove2me | Theorems.Thm_IsIntegrallyClosed_of_faithfullyFlat
-- name    : IsIntegrallyClosed.of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/75eedc41-71d5-5250-b94d-fb97c5eb2f64
-- title:
--   Integral closedness descends along faithfully flat algebras
-- statement:
--   Let $A$ and $B$ be commutative rings, each an integral domain, and let $B$ be an $A$-algebra which is faithfully flat as an $A$-module. Assume $B$ is integrally closed, in the sense of Mathlib's `IsIntegrallyClosed`: every element of the fraction field of $B$ that is integral over $B$ lies in the image of $B$. The conclusion is that $A$ is integrally closed in the same sense, i.e. every element of the fraction field of $A$ integral over $A$ is the image of an element of $A$. No noetherian, finiteness or local hypothesis is imposed, and the injectivity of $A \to B$ is not assumed separately: it is a consequence of faithful flatness.
--
--   This is the descent of normality along a faithfully flat extension of domains. It is used in the study of local rings of algebraic curves, where $B$ is a completion or a model ring: it feeds the criteria [`AlgebraicCurve.mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed`](thm.html#AlgebraicCurve.mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed) and [`IsLocalRing.isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel`](thm.html#IsLocalRing.isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel), which deduce integral closedness of a local ring from the shape of its adic completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_of_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsIntegrallyClosed.of_faithfullyFlat (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] : IsIntegrallyClosed A := by sorry
