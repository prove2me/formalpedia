-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow
-- name    : ModularCurve.FullLevel.AuxLevel.ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/794f150e-55df-56f2-9a91-9235f9c80feb
-- title:
--   Inertia acts on a uniformiser by the mod q cyclotomic character
-- statement:
--   Let $q$ and $\ell$ be primes with $\ell \neq q$, and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{q\ell\}$, i.e. generated over $\mathbb{Q}$ by a primitive $q\ell$-th root of unity. Let $\zeta \in L$ be a primitive $q$-th root of unity. Let $A$ be a commutative domain which is a discrete valuation ring, equipped with an algebra structure over which $L$ is its fraction field, and assume that the image of $q$ in $A$ lies in the maximal ideal $\mathfrak{m}_A$ of $A$ and that $\zeta$ lies in the image of $A$ under the structure map $A \to L$. Let $\varpi \in A$ be a generator of $\mathfrak{m}_A$, so $\mathfrak{m}_A = (\varpi)$. Let $d$ be a unit of $\mathbb{Z}/q$, and let $\sigma_L$ be a ring automorphism of $L$ and $\sigma_A$ a ring automorphism of $A$ which is compatible with $\sigma_L$ in the sense that $\sigma_L$ applied to the image of $a$ equals the image of $\sigma_A(a)$ for every $a \in A$; assume further that $\sigma_A$ is trivial modulo $\mathfrak{m}_A$, i.e. $\sigma_A(a) - a \in \mathfrak{m}_A$ for all $a \in A$, and that $\sigma_L(\zeta) = \zeta^{m}$ where $m$ is the canonical representative in $\{0,\dots,q-1\}$ of $d$. Then $$\sigma_A(\varpi) - m\,\varpi \in \mathfrak{m}_A^{2},$$ with $m$ viewed in $A$ via the natural map from $\mathbb{N}$.
--
--   This is the statement that the tame character describing the action of an inertial automorphism on a uniformiser of a discrete valuation ring above $q$ in the $q\ell$-th cyclotomic field coincides, modulo the square of the maximal ideal, with the mod $q$ cyclotomic character recording the action on $\mu_q$; the ramification index $q-1$ at $q$ is what makes the normalisation exact rather than only exact up to a power. It is used in the computations of the inertia action on the linear part of the Drinfeld chart in the construction of integral models of modular curves of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.AuxLevel.ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A)
    (hσ : ∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a))
    (hinert : ∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A)
    (hd : σL ζ = ζ ^ ((d : ZMod q).val)) :
    σA ϖ - (((d : ZMod q).val : ℕ) : A) * ϖ ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by sorry
