-- Prove2me | Theorems.Thm_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero
-- name    : Function.mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/330b8a37-b890-5a54-8dca-ad0ea8fbb519
-- title:
--   Separation of variables from pairwise dependence in all but one direction
-- statement:
--   Let $\iota$ be a finite type with decidable equality, let $X_i$ be arbitrary types indexed by $i \in \iota$, let $\Phi \colon \prod_{i} X_i \to \mathbb{C}$ be any function, and fix $i_0 \in \iota$. Writing `Function.update` $b\, i\, t$ for the point $b$ with its $i$-th coordinate replaced by $t$, assume that for every $i \neq i_0$ and every pair of base points $b, b' \in \prod_j X_j$ the two one-variable functions $t \mapsto \Phi(b[i \mapsto t])$ and $t \mapsto \Phi(b'[i \mapsto t])$ on $X_i$ are linearly dependent over $\mathbb{C}$, in the sense that there is a pair $c = (c_1, c_2) \in \mathbb{C} \times \mathbb{C}$ with $c \neq 0$ and $c_1 \Phi(b[i \mapsto t]) + c_2 \Phi(b'[i \mapsto t]) = 0$ for all $t \in X_i$. Then for every base point $b_0$ and every $t \in \prod_j X_j$,
--   $$\Phi(t)\, \Phi(b_0)^{\#\iota - 1} = \Phi\bigl(b_0[i_0 \mapsto t_{i_0}]\bigr) \cdot \prod_{i \in \iota \setminus \{i_0\}} \Phi\bigl(b_0[i \mapsto t_i]\bigr),$$
--   the product being over the complement of $i_0$ in $\iota$ and the exponent being the natural-number subtraction $\#\iota - 1$. No hypothesis is imposed in the distinguished direction $i_0$.
--
--   An elementary separation-of-variables statement: a function on a finite product that is "rank one" in each direction other than one distinguished direction factors, through any base point, as the product of its one-variable restrictions, normalised by $\Phi(b_0)^{1-\#\iota}$. It is used in the archimedean analysis of automorphic forms, where one-variable uniqueness at each real place (bounded solutions of the Whittaker equation) yields the pairwise dependence hypothesis, and feeds the bound on Whittaker coefficients in [`AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy`](thm.html#AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Function.mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∀ b b' : ∀ j, X j,
      ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ t : X i, c.1 * Φ (Function.update b i t) + c.2 * Φ (Function.update b' i t) = 0)
    (b₀ t : ∀ j, X j) :
    Φ t * Φ b₀ ^ (Fintype.card ι - 1) =
      Φ (Function.update b₀ i₀ (t i₀)) * ∏ i ∈ Finset.univ.erase i₀, Φ (Function.update b₀ i (t i)) := by sorry
