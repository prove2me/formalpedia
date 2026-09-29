-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension
-- name    : ModularCurve.XOneP.exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/91d94551-ecbf-5a1a-b9fd-f124e3ab58c2
-- title:
--   Residue field 𝔽ₚ for a valuation ring of ℚ(ζₚ)
-- statement:
--   Let $p$ be a prime and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, so that $L$ is generated over $\mathbb{Q}$ by a primitive $p$-th root of unity and contains such a root; let $\zeta \in L$ be a primitive $p$-th root of unity. Let $A$ be a commutative domain which is a discrete valuation ring, equipped with an algebra structure over which $L$ is the fraction field of $A$, and assume that the image of $p$ in $A$ lies in the maximal ideal $\mathfrak{m}_A$ of $A$ and that $\zeta$ lies in the image of the structure map $A \to L$. The conclusion is that for every $a \in A$ there exists an integer $n$ with $a - n \cdot 1_A \in \mathfrak{m}_A$; equivalently, the composite $\mathbb{Z} \to A \to A/\mathfrak{m}_A$ is surjective, so the residue field of $A$ is the prime field $\mathbb{F}_p$ (the hypothesis $p \in \mathfrak{m}_A$ giving the characteristic).
--
--   This records the total ramification of $p$ in $\mathbb{Q}(\zeta_p)$ in the form needed later: any discrete valuation ring with fraction field $\mathbb{Q}(\zeta_p)$ containing $\zeta$ and with $p$ in its maximal ideal has residue field $\mathbb{F}_p$. It is used to produce a ring homomorphism from $A$ to $\mathbb{Z}/p$ compatible with the integer structure map and to show that the Galois action on $A$ is trivial modulo the maximal ideal, in the analysis of the modular curve $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.XOneP.exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ) :
    ∀ a : A, ∃ n : ℤ, a - (n : A) ∈ IsLocalRing.maximalIdeal A := by sorry
