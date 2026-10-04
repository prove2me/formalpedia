-- Prove2me | Theorems.Thm_NumberField_exists_isUnramifiedIn_le_sup_of_prime_ne
-- name    : NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-04T09:27:49.330648+00:00
-- url     : https://prove2.me/theorems/3914fe85-3946-4172-9997-7045d1813ed2
-- title:
--   Kronecker-Weber, tame step: removal of the ramification at a prime $q \ne p$ from an abelian field of $p$-power degree
-- statement:
--   Let $p \ne q$ be primes, let $\Omega$ be an algebraically closed field of characteristic zero (an algebra over $\mathbb{Q}$), and let $E \subseteq \Omega$ be a finite abelian extension of $\mathbb{Q}$ of degree $p^k$. The statement asserts that there are subfields $E', F \subseteq \Omega$ such that
--
--   1. $E'$ is a finite abelian extension of $\mathbb{Q}$ of degree a power of $p$,
--   2. $q$ is unramified in $E'$,
--   3. each prime $\ell$ that is unramified in $E$ is unramified in $E'$,
--   4. $F$ embeds into the cyclotomic field $\mathbb{Q}(\zeta_q)$, and
--   5. $$E \subseteq E' \cdot F .$$
--
--   In words: the ramification of $E$ at the prime $q \ne p$ comes from a subfield of $\mathbb{Q}(\zeta_q)$, and no new ramification appears.
--
--   **Proof idea.** Let $p^a$ be the exact power of $p$ that divides $q - 1$, let $F$ be the subfield of $\mathbb{Q}(\zeta_q)$ of degree $p^a$, and let $L = E \cdot F$. The field $L$ is abelian of $p$-power degree, so its inertia group $I$ at $q$ is tame, and $|I|$ divides $q - 1$, hence $p^a$. The field $F$ is totally ramified at $q$, so $I$ maps onto $\mathrm{Gal}(F/\mathbb{Q})$ and $|I| = p^a$. Let $E'$ be the fixed field of $I$. Then $q$ is unramified in $E'$, $E' \cap F = \mathbb{Q}$, and a degree count gives $E' F = L \supseteq E$. A prime $\ell \ne q$ that is unramified in $E$ is unramified in $F$, hence in $L$, hence in $E'$. If $q$ is already unramified in $E$ (for example $q = 2$, or $k = 0$), take $E' = E$ and $F = \mathbb{Q}$.
--
--   **Use.** Induction on the number of ramified primes different from $p$ reduces the Kronecker-Weber theorem for abelian fields of $p$-power degree to the case of fields unramified outside $p$. This is a child of `Leopoldt.exists_algHom_cyclotomicField_of_isCyclic_primePow`; the compositum is handled by `NumberField.exists_algHom_cyclotomicField_of_sup`.
--
--   **Formalization Note.** Fields are `IntermediateField ℚ Ω`; "abelian" is the Mathlib class `IsAbelianGalois ℚ E`; "$\ell$ unramified in $E$" is `Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(ℓ : ℤ)})`; the existential carries `FiniteDimensional ℚ E'` and `IsAbelianGalois ℚ E'` as propositions. Mathlib (at this revision) has inertia groups (`Ideal.inertia`, `Ideal.card_inertia_eq_ramificationIdxIn`), the inertia field (`IsInertiaField`), ramification in cyclotomic fields (`IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow`, `ramificationIdxIn_eq_of_not_dvd`) and `IsCyclotomicExtension.Rat.galEquivZMod`. It has no higher ramification groups and no tame character $I \to (\mathbb{Z}/q)^\times$, $\sigma \mapsto \sigma(\pi)/\pi$; the divisibility $|I| \mid q - 1$ for an abelian extension of $\mathbb{Q}$ with $q \nmid |I|$ is the main missing piece. A second missing piece is that a prime unramified in two fields is unramified in their compositum.
-- source:
--   The ramification-theoretic proof of the Kronecker-Weber theorem: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14 (cited by chapter); M. J. Greenberg, An elementary proof of the Kronecker-Weber theorem, Amer. Math. Monthly 81 (1974). This is the step that removes one tamely ramified prime with a subfield of $\mathbb{Q}(\zeta_q)$. The statement here uses the subfield of degree equal to the $p$-part of $q-1$, so that only the divisibility $|I_q| \mid q - 1$ for the tame inertia group is necessary.

import Mathlib

open NumberField

theorem NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (E : IntermediateField ℚ Ω) [FiniteDimensional ℚ E] [IsAbelianGalois ℚ E]
    (k : ℕ) (hE : Module.finrank ℚ E = p ^ k) :
    ∃ E' F : IntermediateField ℚ Ω, FiniteDimensional ℚ E' ∧ IsAbelianGalois ℚ E' ∧
      (∃ m : ℕ, Module.finrank ℚ E' = p ^ m) ∧
      Algebra.IsUnramifiedIn (𝓞 E') (Ideal.span {(q : ℤ)}) ∧
      (∀ ℓ : ℕ, ℓ.Prime → Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(ℓ : ℤ)}) →
        Algebra.IsUnramifiedIn (𝓞 E') (Ideal.span {(ℓ : ℤ)})) ∧
      Nonempty (F →ₐ[ℚ] CyclotomicField q ℚ) ∧ E ≤ E' ⊔ F := by sorry
