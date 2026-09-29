-- Prove2me | Theorems.Thm_IsPrimitiveRoot_exists_isPrimitiveRoot_mul_pow_eq_and_mem_and_ringHom_apply_eq_exp_of_henselian
-- name    : IsPrimitiveRoot.exists_isPrimitiveRoot_mul_pow_eq_and_mem_and_ringHom_apply_eq_exp_of_henselian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/52ae3e81-ea0c-59e6-a127-784a53cbdb5c
-- title:
--   Lifting ζ_q to ζ_{qℓ} over a henselian base
-- statement:
--   Let $q$ and $\ell$ be natural numbers, each assumed prime, with $\ell \neq q$. Let $L$ be a field of characteristic zero and let $A$ be a domain which is a discrete valuation ring, henselian as a local ring, with algebraically closed residue field $\mathrm{IsLocalRing.ResidueField}\ A$, equipped with an $A$-algebra structure on $L$ making $L$ a field of fractions of $A$; assume the image of $q$ in $A$ lies in the maximal ideal. Let $\zeta \in L$ be a primitive $q$-th root of unity which lies in the image of the structure map $A \to L$, and suppose there exists a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = \exp(2\pi i/q)$. The conclusion is that there exists $\xi \in L$ which is a primitive $(q\ell)$-th root of unity, satisfies $\xi^{\ell} = \zeta$, lies in the image of $A \to L$, and for which some ring homomorphism $L \to \mathbb{C}$ sends $\xi$ to $\exp\bigl(2\pi i/(q\ell)\bigr)$; the last homomorphism is produced existentially and need not be the given $\iota$.
--
--   This is the standard step that enlarges a chosen $q$-th root of unity, together with its fixed complex normalisation, to a compatible $(q\ell)$-th root over a henselian discrete valuation ring with algebraically closed residue field, using Hensel's lemma for $X^{\ell}-1$ (separable over the residue field as $\ell \neq q$) and a Chinese-remainder choice of exponents. It is used in the construction of charts and level structures on modular curves at tame level, where data framed only by $\zeta_q$ must be upgraded to $\Gamma_1(\ell)$-level framings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsPrimitiveRoot_exists_isPrimitiveRoot_mul_pow_eq_and_mem_and_ringHom_apply_eq_exp_of_henselian.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsPrimitiveRoot.exists_isPrimitiveRoot_mul_pow_eq_and_mem_and_ringHom_apply_eq_exp_of_henselian
    (q ℓ : ℕ) [Fact q.Prime] [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (ζ : L) (hζ : IsPrimitiveRoot ζ q) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q)) :
    ∃ ξ : L, IsPrimitiveRoot ξ (q * ℓ) ∧ ξ ^ ℓ = ζ ∧ (∃ x : A, algebraMap A L x = ξ) ∧
      ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by sorry
