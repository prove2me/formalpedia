-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_finite_quotient_maximalIdeal_of_isFractionRing
-- name    : IsDiscreteValuationRing.finite_quotient_maximalIdeal_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/c6e0b32b-aae8-52e7-90e5-4284d9deb541
-- title:
--   Finite residue field of a DVR inside a number field
-- statement:
--   Let $A$ be a commutative domain which is a discrete valuation ring, and let $L$ be a field of characteristic zero which is an $A$-algebra and a fraction field of $A$ (so that the structure map $A \to L$ realises $L$ as the localisation of $A$ at its nonzero elements), and which is finite-dimensional as a $\mathbb{Q}$-vector space. Let $p$ be a prime number whose image in $A$ lies in the maximal ideal $\mathfrak{m}_A$ of the local ring $A$. The conclusion is that the residue ring $A/\mathfrak{m}_A$ is a finite type, i.e. the residue field of $A$ is finite. Only finiteness is asserted; the sharper bound $\#(A/\mathfrak{m}_A) \le p^{[L:\mathbb{Q}]}$ that the argument produces is not part of the statement.
--
--   This is the standard fact that a discrete valuation ring whose fraction field is a number field has finite residue field, here in the form needed when the residual characteristic $p$ is given in advance by membership of $p$ in the maximal ideal. It is used in the analysis of integral models of the modular curves $X_0(p)$ and $X_1(p)/X_0(p)$, where residue fields of local rings at points of such models must be known to be finite, for instance in computing inertia and chart data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_finite_quotient_maximalIdeal_of_isFractionRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.finite_quotient_maximalIdeal_of_isFractionRing (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type*) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L] [FiniteDimensional ℚ L]
    (p : ℕ) [Fact p.Prime] (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    Finite (A ⧸ IsLocalRing.maximalIdeal A) := by sorry
