-- Prove2me | Theorems.Thm_NumberField_isUnramifiedIn_sup
-- name    : NumberField.isUnramifiedIn_sup
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-04T10:10:41.30065+00:00
-- url     : https://prove2.me/theorems/656f45c5-201d-443f-be07-4e080fdc56de
-- title:
--   A prime unramified in two number fields is unramified in their compositum
-- statement:
--   Let $\Omega$ be a field of characteristic zero, let $E_1, E_2 \subseteq \Omega$ be number fields (subfields that are finite over $\mathbb{Q}$), and let $\ell$ be a prime number. Assume that $\ell$ is unramified in $E_1$ and in $E_2$. The statement asserts that $\ell$ is unramified in the compositum:
--
--   $$\ell \text{ unramified in } E_1 \text{ and } E_2 \implies \ell \text{ unramified in } E_1 \cdot E_2 .$$
--
--   No Galois hypothesis is necessary.
--
--   **Proof idea.** Local proof: the completion of $E_1 E_2$ at a prime over $\ell$ is the compositum of completions of $E_1$ and $E_2$, and a compositum of unramified extensions of $\mathbb{Q}_\ell$ is unramified. Global proof: after localization at $\ell$, the ring $\mathcal{O}_{E_1} \otimes_{\mathbb{Z}} \mathcal{O}_{E_2}$ is finite étale over $\mathbb{Z}_{(\ell)}$; its image in $E_1 E_2$ is a finite étale domain, hence normal, hence equal to the localized ring of integers of $E_1 E_2$. A third proof for Galois fields uses inertia groups: the inertia group of the compositum embeds in the product of the two inertia groups.
--
--   **Use.** A child of the tame step `NumberField.exists_isUnramifiedIn_le_sup_of_prime_ne` of the Kronecker-Weber theorem. There it is used for abelian fields only.
--
--   **Formalization Note.** "Unramified" is `Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(ℓ : ℤ)})`, where `𝓞 E` is the integral closure of `ℤ` in `E`. The compositum is `E₁ ⊔ E₂ : IntermediateField ℚ Ω`. The hypothesis `hℓ` is not necessary for the truth of the statement. Mathlib has `NumberField.not_dvd_discr_iff_isUnramifiedIn` (an integer prime is unramified if and only if it does not divide the discriminant); it has no statement on the discriminant or the ramification of a compositum.
-- source:
--   The ramification-theoretic proof of the Kronecker-Weber theorem: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14 (cited by chapter); M. J. Greenberg, An elementary proof of the Kronecker-Weber theorem, Amer. Math. Monthly 81 (1974). Standard.

import Mathlib

open NumberField

theorem NumberField.isUnramifiedIn_sup {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (E₁ E₂ : IntermediateField ℚ Ω) [FiniteDimensional ℚ E₁] [FiniteDimensional ℚ E₂]
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h₁ : Algebra.IsUnramifiedIn (𝓞 E₁) (Ideal.span {(ℓ : ℤ)}))
    (h₂ : Algebra.IsUnramifiedIn (𝓞 E₂) (Ideal.span {(ℓ : ℤ)})) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) (Ideal.span {(ℓ : ℤ)}) := by sorry
