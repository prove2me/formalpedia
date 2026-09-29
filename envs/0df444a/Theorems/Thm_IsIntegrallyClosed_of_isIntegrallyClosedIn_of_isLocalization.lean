-- Prove2me | Theorems.Thm_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization
-- name    : IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/631599f7-7ca6-5589-906b-ddcff44f67e7
-- title:
--   Integral closedness descends from a localisation
-- statement:
--   Let $C$ be a commutative ring which is a domain, let $M$ be a submonoid of $C$ contained in the non-zero-divisors of $C$, and let $L$ be a commutative ring which is a domain, equipped with a $C$-algebra structure making it a localisation of $C$ at $M$. Assume further that $C$ is integrally closed in $L$, i.e. every element of $L$ that is integral over $C$ lies in the image of the structure map $C \to L$, and that $L$ is integrally closed, i.e. every element of the fraction field of $L$ that is integral over $L$ lies in the image of $L$. Then $C$ is integrally closed: every element of the fraction field of $C$ which is integral over $C$ already comes from $C$. (The hypothesis $M \le$ non-zero-divisors is what makes the localisation map $C \to L$ injective and identifies the fraction fields of $C$ and $L$.)
--
--   This is the standard descent of normality along a localisation, in the elementary form used for models over a discrete valuation ring: normality of $C$ follows from normality of $C[1/\varpi]$ together with $C$ being integrally closed in $C[1/\varpi]$. It is applied in the proof that a tensor product with reduced special fibre is a normal domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C := by sorry
