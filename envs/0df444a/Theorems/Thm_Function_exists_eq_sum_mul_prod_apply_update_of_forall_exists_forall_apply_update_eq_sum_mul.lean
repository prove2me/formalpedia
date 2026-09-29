-- Prove2me | Theorems.Thm_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul
-- name    : Function.exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/116f27ff-6fba-5240-8596-31b8c19e4367
-- title:
--   Finite-rank partial spans give a finite sum of products
-- statement:
--   Let $\iota$ be a finite type with decidable equality, let $X : \iota \to \mathrm{Type}$ be a family of types, let $\Phi : \bigl(\prod_{j} X j\bigr) \to \mathbb{C}$ be a function on the product, and let $i_0 \in \iota$ be a distinguished index. Assume that for every index $i \neq i_0$ there are a natural number $d$ and functions $\varphi_0,\dots,\varphi_{d-1} : X i \to \mathbb{C}$ (indexed by `Fin d`, depending on $i$ but not on any base point) such that for every $b \in \prod_j X j$ there are scalars $c_0,\dots,c_{d-1} \in \mathbb{C}$ with $\Phi\bigl(\mathrm{update}(b, i, t)\bigr) = \sum_k c_k \varphi_k(t)$ for all $t \in X i$; that is, each partial function of $\Phi$ in the direction $i$ lies in the span of finitely many fixed functions on $X i$, uniformly in the base point. No hypothesis is imposed in the direction $i_0$. The conclusion is the existence of a natural number $m$, coefficients $\mathrm{coef} : \mathrm{Fin}\,m \to \mathbb{C}$ and base points $\beta : \mathrm{Fin}\,m \to \iota \to \prod_j X j$ such that for every $t \in \prod_j X j$ one has $\Phi(t) = \sum_{\alpha} \mathrm{coef}(\alpha) \prod_{i \in \iota} \Phi\bigl(\mathrm{update}(\beta(\alpha, i), i, t_i)\bigr)$, the product being over all indices $i$, including $i_0$.
--
--   This is a separation-of-variables statement in finite-rank form: finite-dimensionality of the spans of the one-variable partial functions of $\Phi$ in all directions but one forces $\Phi$ to be a finite sum of products of its own partial functions, each taken through a fixed base point. It is used in the proof of the bound on Whittaker coefficients of a pure automorphic form at the identity in terms of a power of the idele norm, where the factorisation through one-variable data at each place is what makes the estimate available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Function.exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∃ (m : ℕ) (coef : Fin m → ℂ) (β : Fin m → ι → ∀ j, X j),
      ∀ t : ∀ j, X j, Φ t = ∑ α, coef α * ∏ i, Φ (Function.update (β α i) i (t i)) := by sorry
