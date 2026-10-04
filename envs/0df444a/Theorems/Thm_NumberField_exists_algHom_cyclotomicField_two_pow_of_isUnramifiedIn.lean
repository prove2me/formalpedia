-- Prove2me | Theorems.Thm_NumberField_exists_algHom_cyclotomicField_two_pow_of_isUnramifiedIn
-- name    : NumberField.exists_algHom_cyclotomicField_two_pow_of_isUnramifiedIn
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-04T09:27:59.769374+00:00
-- url     : https://prove2.me/theorems/6a397989-c48a-4097-822d-0ce14ef63a62
-- title:
--   Kronecker-Weber, wild step for $p = 2$: an abelian field of degree $2^k$ unramified outside $2$ lies in $\mathbb{Q}(\zeta_{2^N})$
-- statement:
--   Let $K$ be a finite abelian extension of $\mathbb{Q}$ of degree $2^k$. Assume that each odd prime $\ell$ is unramified in $K$. The statement asserts that there is $N \ge 0$ and an embedding of fields
--   $$K \hookrightarrow \mathbb{Q}(\zeta_{2^N}) .$$
--
--   **Proof idea.** The quadratic fields unramified outside $2$ are $\mathbb{Q}(i)$, $\mathbb{Q}(\sqrt{2})$ and $\mathbb{Q}(\sqrt{-2})$, by Minkowski's bound or a discriminant computation. If $K$ is real, its Galois group has exactly one subgroup of index $2$ (the only real quadratic field unramified outside $2$ is $\mathbb{Q}(\sqrt 2)$), so it is cyclic, and $K$ is the real subfield of degree $2^k$ of $\mathbb{Q}(\zeta_{2^{k+2}})$ by the compositum argument of the odd case. In general, $K(i)$ is abelian of $2$-power degree and unramified outside $2$, and it is the compositum of $\mathbb{Q}(i)$ and its maximal real subfield, so $K \subseteq K(i) \subseteq \mathbb{Q}(\zeta_{2^N})$.
--
--   **Use.** With the tame step (`NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne`) this gives the Kronecker-Weber theorem for abelian fields of $2$-power degree. This is a child of `Leopoldt.exists_algHom_cyclotomicField_of_isCyclic_primePow`.
--
--   **Formalization Note.** "Abelian" is `IsAbelianGalois ℚ K`; "$\ell$ unramified in $K$" is `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)})`; the conclusion is `Nonempty (K →ₐ[ℚ] CyclotomicField (2 ^ N) ℚ)`. For $k = 0$ take $N = 0$. The platform has the quadratic case (`NumberField.exists_algHom_cyclotomicField_of_finrank_le_two`) and the exponent-two case (`NumberField.exists_algHom_cyclotomicField_of_exponent_two`), but with an unspecified cyclotomic field; here the conductor must be a power of $2$. Mathlib has `ZMod.isCyclic_units_two_pow_iff`, `ZMod.orderOf_five` and `IsCyclotomicExtension.Rat.galEquivZMod`.
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14 (cited by chapter): the case $p = 2$ of the Kronecker-Weber theorem for fields in which only $2$ ramifies; see also M. J. Greenberg, Amer. Math. Monthly 81 (1974).

import Mathlib

open NumberField

theorem NumberField.exists_algHom_cyclotomicField_two_pow_of_isUnramifiedIn
    (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] (k : ℕ)
    (hK : Module.finrank ℚ K = 2 ^ k)
    (hunr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)})) :
    ∃ N : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField (2 ^ N) ℚ) := by sorry
