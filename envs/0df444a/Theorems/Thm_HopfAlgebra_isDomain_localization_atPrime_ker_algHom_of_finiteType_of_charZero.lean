-- Prove2me | Theorems.Thm_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
-- name    : HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/c8ce09d2-80c6-5ab6-b58b-648080d180b8
-- title:
--   Localization at any K-point kernel of a Hopf algebra is a domain
-- statement:
--   Let $K$ be a field of characteristic zero and let $A$ be a commutative ring carrying a $K$-Hopf-algebra structure which is of finite type as a $K$-algebra, and let $\chi \colon A \to K$ be a homomorphism of $K$-algebras. The kernel of the underlying ring homomorphism of $\chi$ is a prime ideal of $A$ (it is the kernel of a ring homomorphism onto the field $K$, and this instance is supplied inside the statement itself). The assertion is that the localization of $A$ at this prime, $\mathrm{Localization.AtPrime}(\ker \chi)$, is an integral domain, i.e. a nontrivial commutative ring with no zero divisors. Thus every $K$-rational point of $\mathrm{Spec}\,A$ has integral local ring, with no smoothness, reducedness or connectedness hypothesis imposed on $A$ beyond finite type and characteristic zero.
--
--   This is steps (i)–(iii) of Cartier's theorem that a Hopf algebra of finite type over a field of characteristic zero is reduced (equivalently, that affine group schemes of finite type in characteristic zero are smooth), here in the local form at an arbitrary $K$-point rather than only at the identity. It is used, together with the weak Nullstellensatz and the local-to-global criterion for reducedness, to prove [`HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero`](thm.html#HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A]
    (χ : A →ₐ[K] K) :
    haveI : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
    IsDomain (Localization.AtPrime (RingHom.ker χ.toRingHom)) := by sorry
