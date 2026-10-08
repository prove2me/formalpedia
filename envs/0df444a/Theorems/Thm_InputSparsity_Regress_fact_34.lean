-- Prove2me | Theorems.Thm_InputSparsity_Regress_fact_34
-- name    : InputSparsity.Regress.fact_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:03:01.61962+00:00
-- url     : https://prove2.me/theorems/82b46f42-6bb0-4ce4-8e5e-737dd42dfcd2
-- title:
--   Fact 34, p. 23 — Pythagorean theorem: CᵀD = 0 implies ‖C + D‖_F² = ‖C‖_F² + ‖D‖_F²
-- statement:
--   Let $C$ and $D$ be real $n\times m$ matrices (the same number of rows and of columns). If $C^\top D=0$, then
--   $$\|C+D\|_F^2=\|C\|_F^2+\|D\|_F^2 .$$
--
--   This is the matrix (Frobenius) form of the Pythagorean theorem. Combined with the normal equations (Fact 35) it splits the regression error into an irreducible part and a part caused by a suboptimal solution, which is the first step of the proof of Theorem 36.
--
--   **Formalization Note** $\|\cdot\|_F^2$ is the explicit sum of squared entries.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 23, Fact 34

import Mathlib
import Definitions.Def_InputSparsity_Regress_Basic

namespace InputSparsity.Regress
open Matrix

theorem fact_34 {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) (h : Cᵀ * D = 0) :
    InputSparsity.Embed.frobSq (C + D) = InputSparsity.Embed.frobSq C + InputSparsity.Embed.frobSq D := by sorry

end InputSparsity.Regress
