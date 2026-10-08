-- Prove2me | Theorems.Thm_InputSparsity_Regress_fact_35
-- name    : InputSparsity.Regress.fact_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:03:05.75254+00:00
-- url     : https://prove2.me/theorems/c3269ffc-abb6-495e-91b2-98985e044ef4
-- title:
--   Fact 35, p. 23 — normal equations: X* = C⁻D solves min ‖CX − D‖_F², Cᵀ(CX* − D) = 0, and the error splits
-- statement:
--   Let $C$ be a real $n\times d$ matrix and $D$ a real $n\times d'$ matrix, and consider the multiple-response least-squares problem
--   $$\min_{X\in\mathbb R^{d\times d'}}\|CX-D\|_F^2 .$$
--   Then:
--
--   1. $C$ has a Moore–Penrose inverse $C^-$ (a $d\times n$ matrix satisfying the four Penrose equations), and for every such $C^-$ the matrix $X^*=C^-D$ is a minimizer.
--   2. Every minimizer $X^*$ satisfies the normal equations $C^\top(CX^*-D)=0$.
--   3. Consequently $c^\top(CX^*-D)=0$ for every vector $c=Cx$ in the column space of $C$.
--   4. For every minimizer $X^*$ and every $X\in\mathbb R^{d\times d'}$,
--   $$\|CX-D\|_F^2=\|C(X-X^*)\|_F^2+\|CX^*-D\|_F^2 .$$
--
--   The identity in 4 says that the excess error of any $X$ is exactly $\|C(X-X^*)\|_F^2$; Theorem 36 bounds this quantity for the sketched solution.
--
--   **Formalization Note** The paper writes "the solution"; when $C$ is rank-deficient minimizers are not unique, so items 2–4 are stated for every minimizer, which is stronger than for $C^-D$ alone. The pseudoinverse enters only through the Penrose equations. In item 3 the row vector $c^\top M$ is Lean's `vecMul`.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 23, Fact 35

import Mathlib
import Definitions.Def_InputSparsity_Regress_Basic

namespace InputSparsity.Regress
open Matrix

theorem fact_35 {n d d' : ℕ} (C : Matrix (Fin n) (Fin d) ℝ) (D : Matrix (Fin n) (Fin d') ℝ) :
    (∃ G : Matrix (Fin d) (Fin n) ℝ, IsMoorePenrose C G) ∧
    (∀ G : Matrix (Fin d) (Fin n) ℝ, IsMoorePenrose C G → IsLSMinimizer C D (G * D)) ∧
    (∀ Xstar : Matrix (Fin d) (Fin d') ℝ, IsLSMinimizer C D Xstar →
      Cᵀ * (C * Xstar - D) = 0 ∧
      (∀ x : Fin d → ℝ, (C *ᵥ x) ᵥ* (C * Xstar - D) = 0) ∧
      (∀ X : Matrix (Fin d) (Fin d') ℝ,
        InputSparsity.Embed.frobSq (C * X - D) = InputSparsity.Embed.frobSq (C * (X - Xstar)) + InputSparsity.Embed.frobSq (C * Xstar - D))) := by sorry

end InputSparsity.Regress
