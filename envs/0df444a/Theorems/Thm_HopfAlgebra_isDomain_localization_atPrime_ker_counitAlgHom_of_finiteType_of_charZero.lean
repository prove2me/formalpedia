-- Prove2me | Theorems.Thm_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
-- name    : HopfAlgebra.isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/03da3f15-7c05-5db2-a4ba-85ed681d1f9f
-- title:
--   Localization at the augmentation ideal is a domain
-- statement:
--   Let $K$ be a field of characteristic zero and let $A$ be a commutative ring carrying the structure of a Hopf algebra over $K$ which is of finite type as a $K$-algebra. Write $\varepsilon =$ `Bialgebra.counitAlgHom K A` for the counit, viewed as a ring homomorphism $A \to K$, and $I = \ker \varepsilon$ for the augmentation ideal. Since the target is a field, $I$ is a prime ideal of $A$ (this is recorded inside the statement by `RingHom.ker_isPrime`, supplying the instance needed to form the localization at $I$). The assertion is that the localization `Localization.AtPrime` of $A$ at the prime $I$, i.e. $A_I$, is an integral domain: it is a nontrivial commutative ring without zero divisors. No hypothesis is placed on $A$ beyond commutativity, the Hopf algebra structure over $K$, and finite generation as a $K$-algebra, and none on $K$ beyond being a field of characteristic zero.
--
--   This is the local form of steps (i)–(ii) of Cartier's theorem that a group scheme of finite type over a field of characteristic zero is reduced, specialised to the augmentation point. It is used to deduce the same conclusion at an arbitrary $K$-point, in [`HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero`](thm.html#HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero), by translating the point to the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    haveI : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
      RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
    IsDomain (Localization.AtPrime (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)) := by sorry
