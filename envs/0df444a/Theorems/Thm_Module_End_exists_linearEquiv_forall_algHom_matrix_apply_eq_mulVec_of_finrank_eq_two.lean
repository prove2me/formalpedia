-- Prove2me | Theorems.Thm_Module_End_exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two
-- name    : Module.End.exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e6b60c3e-02c4-5c2e-80a6-e3c6fca6e29c
-- title:
--   A two-dimensional M₂(k)-module is the standard one
-- statement:
--   Let $k$ be a field and $W$ a finite-dimensional $k$-vector space with $\dim_k W = 2$, and let $\psi \colon M_2(k) \to \operatorname{End}_k(W)$ be a homomorphism of unital $k$-algebras, where $M_2(k)$ is the algebra of matrices indexed by `Fin 2` and $\operatorname{End}_k(W)$ is the algebra of $k$-linear endomorphisms of $W$. The assertion is that there exists a $k$-linear isomorphism $e \colon W \xrightarrow{\sim} (\mathrm{Fin}\,2 \to k) = k^2$ such that for every matrix $m \in M_2(k)$ and every $w \in W$ one has $e(\psi(m)\,w) = m \cdot e(w)$, the right-hand side being multiplication of the column vector $e(w)$ by $m$ (`Matrix.mulVec`). Thus, after a suitable choice of coordinates on $W$, the given action of the matrix algebra is the standard action of $M_2(k)$ on column vectors; the isomorphism $e$ is produced existentially, with no normalisation imposed on it.
--
--   This is the statement that, up to isomorphism, the only two-dimensional unital module over $M_2(k)$ is the standard module $k^2$ — a special case of the classification of modules over a simple Artinian ring. It is used in the Čerednik–Drinfeld part of the development, by [`CerednikDrinfeld.SpecialModule.exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit`](thm.html#CerednikDrinfeld.SpecialModule.exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit), to put a matrix action into standard form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two
    (k : Type*) [Field k] (W : Type*) [AddCommGroup W] [Module k W] [Module.Finite k W]
    (hW : Module.finrank k W = 2) (ψ : Matrix (Fin 2) (Fin 2) k →ₐ[k] (W →ₗ[k] W)) :
    ∃ e : W ≃ₗ[k] (Fin 2 → k), ∀ (m : Matrix (Fin 2) (Fin 2) k) (w : W), e (ψ m w) = m.mulVec (e w) := by sorry
