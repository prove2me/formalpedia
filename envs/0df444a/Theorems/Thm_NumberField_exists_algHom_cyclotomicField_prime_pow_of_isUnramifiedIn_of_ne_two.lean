-- Prove2me | Theorems.Thm_NumberField_exists_algHom_cyclotomicField_prime_pow_of_isUnramifiedIn_of_ne_two
-- name    : NumberField.exists_algHom_cyclotomicField_prime_pow_of_isUnramifiedIn_of_ne_two
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-04T09:27:48.568979+00:00
-- url     : https://prove2.me/theorems/d5be5bf9-6538-4338-9c36-56b98b18a2e7
-- title:
--   Kronecker-Weber, wild step for odd $p$: an abelian field of degree $p^k$ unramified outside $p$ lies in $\mathbb{Q}(\zeta_{p^N})$
-- statement:
--   Let $p$ be an odd prime and let $K$ be a finite abelian extension of $\mathbb{Q}$ of degree $p^k$. Assume that each prime $\ell \ne p$ is unramified in $K$. The statement asserts that there is $N \ge 0$ and an embedding of fields
--   $$K \hookrightarrow \mathbb{Q}(\zeta_{p^N}) .$$
--
--   **Proof idea.** The key fact is that for odd $p$ there is exactly one cyclic extension of $\mathbb{Q}$ of degree $p$ that is unramified outside $p$, namely the subfield of degree $p$ of $\mathbb{Q}(\zeta_{p^2})$. It follows that the Galois group of $K$ has at most one subgroup of index $p$, so it is cyclic. Let $K_m$ be the subfield of degree $p^m$ of $\mathbb{Q}(\zeta_{p^{m+1}})$ with $p^m = [K : \mathbb{Q}]$. The compositum $K K_m$ is abelian of $p$-power degree and unramified outside $p$, so its Galois group is cyclic by the same argument; it has the two quotients of order $p^m$ that correspond to $K$ and $K_m$, hence $K = K_m$.
--
--   **Use.** With the tame step (`NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne`) this gives the Kronecker-Weber theorem for abelian fields of odd prime-power degree. This is a child of `Leopoldt.exists_algHom_cyclotomicField_of_isCyclic_primePow`.
--
--   **Formalization Note.** "Abelian" is `IsAbelianGalois ℚ K`; "$\ell$ unramified in $K$" is `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)})`; the conclusion is `Nonempty (K →ₐ[ℚ] CyclotomicField (p ^ N) ℚ)`. For $k = 0$ take $N = 0$. The hypothesis $p \ne 2$ is necessary for the uniqueness argument: there are three quadratic fields unramified outside $2$. Mathlib has `ZMod.isCyclic_units_of_prime_pow`, `IsCyclotomicExtension.Rat.galEquivZMod`, Minkowski's theorem (`NumberField.exists_not_isUnramifiedIn`) and Kummer theory (`Mathlib.FieldTheory.KummerExtension`). The uniqueness of the cyclic degree $p$ field unramified outside $p$ is the hard part and is not in Mathlib.
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14 (cited by chapter): the case of an abelian extension of $\mathbb{Q}$ of odd prime-power degree in which only $p$ ramifies; see also M. J. Greenberg, Amer. Math. Monthly 81 (1974).

import Mathlib

open NumberField

theorem NumberField.exists_algHom_cyclotomicField_prime_pow_of_isUnramifiedIn_of_ne_two
    (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] (p k : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Module.finrank ℚ K = p ^ k)
    (hunr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(ℓ : ℤ)})) :
    ∃ N : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField (p ^ N) ℚ) := by sorry
