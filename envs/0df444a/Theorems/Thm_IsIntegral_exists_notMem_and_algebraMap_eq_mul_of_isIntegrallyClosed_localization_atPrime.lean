-- Prove2me | Theorems.Thm_IsIntegral_exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime
-- name    : IsIntegral.exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/635cdef8-184d-50c7-92c9-6724a5f64dd4
-- title:
--   Denominator outside q for elements integral over B
-- statement:
--   Let $B$ and $F$ be commutative rings with $F$ a $B$-algebra, let $M$ be a submonoid of $B$ all of whose elements are non-zero-divisors ($M \le \mathrm{nonZeroDivisors}\,B$), and suppose $F$ is a localisation of $B$ at $M$. Let $\mathfrak q$ be a prime ideal of $B$ and assume that the localisation `Localization.AtPrime 𝔮`, i.e. $B_{\mathfrak q}$, is an integral domain and is integrally closed in its fraction field. Let $t \in F$ be integral over $B$, i.e. $t$ is a root of some monic polynomial with coefficients in $B$ mapped into $F$. Then there exist $s \in B$ with $s \notin \mathfrak q$ and $c \in B$ such that the images in $F$ satisfy $\mathrm{algebraMap}\,c = \mathrm{algebraMap}\,s \cdot t$; that is, $s\,t$ lies in the image of $B$ in $F$, with the multiplier $s$ chosen outside $\mathfrak q$. No integrality or domain hypothesis is imposed on $B$ or $F$ themselves beyond those listed.
--
--   This is the local form of the statement that integral closure commutes with localisation: an element of $M^{-1}B$ integral over $B$ already becomes integral, hence integral-with-denominator, after passing to a normal local ring $B_{\mathfrak q}$, so that the conductor of $B[t]$ into $B$ is not contained in $\mathfrak q$. It serves as an input to [`IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing`](thm.html#IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing), where normality of a local ring is deduced from regularity in smaller dimensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegral_exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsIntegral.exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime
    {B F : Type*} [CommRing B] [CommRing F] [Algebra B F]
    (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) [IsLocalization M F]
    (𝔮 : Ideal B) [𝔮.IsPrime] [IsDomain (Localization.AtPrime 𝔮)] [IsIntegrallyClosed (Localization.AtPrime 𝔮)]
    (t : F) (ht : IsIntegral B t) :
    ∃ s : B, s ∉ 𝔮 ∧ ∃ c : B, algebraMap B F c = algebraMap B F s * t := by sorry
