-- Prove2me | Theorems.Thm_IsCyclotomicExtension_Rat_exists_intermediateField_finrank_eq_of_dvd_sub_one
-- name    : IsCyclotomicExtension.Rat.exists_intermediateField_finrank_eq_of_dvd_sub_one
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T10:10:32.013613+00:00
-- url     : https://prove2.me/theorems/1f02aa4f-acb4-4255-985d-cff2ef090cf4
-- title:
--   The subfield of $\mathbb{Q}(\zeta_q)$ of degree $e \mid q-1$: abelian, totally ramified at $q$, unramified elsewhere
-- statement:
--   Let $\Omega$ be an algebraically closed field of characteristic zero, let $q$ be a prime number, and let $e$ be a divisor of $q - 1$. The statement asserts that there is a subfield $F \subseteq \Omega$ such that
--
--   1. $F$ is a finite abelian extension of $\mathbb{Q}$ of degree $[F : \mathbb{Q}] = e$,
--   2. $F$ embeds into the cyclotomic field $\mathbb{Q}(\zeta_q)$,
--   3. $q$ is totally ramified in $F$: the ramification index of $q$ in $F$ is $e$, and
--   4. each prime $\ell \ne q$ is unramified in $F$.
--
--   **Proof idea.** The group $\mathrm{Gal}(\mathbb{Q}(\zeta_q)/\mathbb{Q}) \cong (\mathbb{Z}/q)^\times$ is cyclic of order $q - 1$, so it has a subgroup of index $e$. Let $F$ be the image in $\Omega$ of its fixed field. The prime $q$ is totally ramified in $\mathbb{Q}(\zeta_q)$, so it is totally ramified in each subfield. The discriminant of $\mathbb{Q}(\zeta_q)$ is a power of $q$ up to sign, so each prime $\ell \ne q$ is unramified in $\mathbb{Q}(\zeta_q)$ and in $F$.
--
--   **Use.** A child of the tame step `NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne` of the Kronecker-Weber theorem, used with $e$ equal to the $p$-part of $q - 1$.
--
--   **Formalization Note.** `F` is an `IntermediateField ℚ Ω`; the existential carries `FiniteDimensional ℚ F` and `IsAbelianGalois ℚ F` as propositions. The ramification index is `(Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 F)` and "unramified" is `Algebra.IsUnramifiedIn`. For $q = 2$ the only case is $e = 1$ and $F = \mathbb{Q}$. Mathlib has `IsCyclotomicExtension.Rat.galEquivZMod`, `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow`, `ramificationIdxIn_eq_of_not_dvd`, and the discriminant of prime cyclotomic fields. The instances `IsAbelianGalois ℚ F` (through `DivisionRing.toRatAlgebra`) and `Module.finrank ℚ F` (through the `ℚ`-algebra structure of `Ω`) agree only by `Subsingleton.elim`.
-- source:
--   The ramification-theoretic proof of the Kronecker-Weber theorem: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14 (cited by chapter); M. J. Greenberg, An elementary proof of the Kronecker-Weber theorem, Amer. Math. Monthly 81 (1974). Standard facts on the cyclotomic field of prime conductor.

import Mathlib

open NumberField

theorem IsCyclotomicExtension.Rat.exists_intermediateField_finrank_eq_of_dvd_sub_one
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (q e : ℕ) (hq : q.Prime)
    (he : e ∣ q - 1) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧ IsAbelianGalois ℚ F ∧
      Module.finrank ℚ F = e ∧
      Nonempty (F →ₐ[ℚ] CyclotomicField q ℚ) ∧
      (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 F) = e ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(ℓ : ℤ)}) := by sorry
