-- Prove2me | Theorems.Thm_NumberField_exists_algHom_cyclotomicField_of_sup
-- name    : NumberField.exists_algHom_cyclotomicField_of_sup
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:48:31.069675+00:00
-- url     : https://prove2.me/theorems/8ad46caf-0b2b-4311-8d68-25b4eb3c0167
-- title:
--   A compositum of subfields of cyclotomic fields lies in a cyclotomic field
-- statement:
--   Let $\Omega$ be a field of characteristic $0$ and let $E_1, E_2 \subseteq \Omega$ be subfields. Suppose that for $i = 1, 2$ there is an integer $n_i \ge 1$ and an embedding of $\mathbb{Q}$-algebras $E_i \hookrightarrow \mathbb{Q}(\zeta_{n_i})$. Then the compositum $E_1 E_2 \subseteq \Omega$ also embeds into a cyclotomic field: there is $n \ge 1$ (one may take $n = n_1 n_2$) and a $\mathbb{Q}$-algebra embedding
--   $$E_1 E_2 \hookrightarrow \mathbb{Q}(\zeta_n).$$
--
--   This is the step of the reduction of the Kronecker–Weber theorem to cyclic extensions of prime-power degree which says that the set of subfields of cyclotomic fields is closed under composita ($\mathbb{Q}(\zeta_m)\mathbb{Q}(\zeta_n) \subseteq \mathbb{Q}(\zeta_{mn})$).
--
--   **Formalization note.** $E_1, E_2$ are `IntermediateField ℚ Ω`, the compositum is `E₁ ⊔ E₂`, $\mathbb{Q}(\zeta_n)$ is `CyclotomicField n ℚ`, and "embeds" means there is some `→ₐ[ℚ]` map (automatically injective).
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14, proof of Theorem 14.1 (reduction step: the compositum of fields contained in cyclotomic fields is contained in a cyclotomic field, since Q(zeta_m)Q(zeta_n) is contained in Q(zeta_mn)).

import Mathlib.NumberTheory.Cyclotomic.Basic

theorem NumberField.exists_algHom_cyclotomicField_of_sup {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (E₁ E₂ : IntermediateField ℚ Ω)
    (h₁ : ∃ n : ℕ, 0 < n ∧ Nonempty (E₁ →ₐ[ℚ] CyclotomicField n ℚ))
    (h₂ : ∃ n : ℕ, 0 < n ∧ Nonempty (E₂ →ₐ[ℚ] CyclotomicField n ℚ)) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (↥(E₁ ⊔ E₂) →ₐ[ℚ] CyclotomicField n ℚ) := by sorry
