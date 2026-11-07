-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_posSemidef_iff_schurStep
-- name    : ModernConvex.Relaxations.posSemidef_iff_schurStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:56:45.023197+00:00
-- url     : https://prove2.me/theorems/5bab9d50-cb31-4cb0-b5bb-9cb46b76d51f
-- title:
--   At a positive pivot, semidefiniteness is equivalent to semidefiniteness of the Schur complement
-- statement:
--   **The induction step of the PSD oracle.**
--
--   Let $M$ be a real symmetric matrix of order $n$ and let $i$ be an index with $M_{ii}>0$. Then
--   $$M\succeq 0 \quad\Longleftrightarrow\quad \texttt{schurStep}\ M\ i\succeq0,$$
--   where $\texttt{schurStep}\ M\ i=M_{\ne i,\ne i}-M_{\ne i,i}M_{ii}^{-1}M_{i,\ne i}$ is the Schur complement at the pivot $i$.
--
--   *($\Leftarrow$)* By completing the square, $v^{\mathsf T}Mv=M_{ii}(v_i+M_{ii}^{-1}\sum_{j\ne i}M_{ij}v_j)^2+Q_i(v)$, where $Q_i$ is the Schur form. The first term is nonnegative because $M_{ii}>0$; the second equals $w^{\mathsf T}(\texttt{schurStep}\ M\ i)w$ for $w$ the restriction of $v$ to the indices $\ne i$ (the Schur form ignores the $i$-th coordinate), hence is nonnegative by hypothesis.
--
--   *($\Rightarrow$)* Given $w$ on the indices $\ne i$, extend it by $0$ at $i$ and then set
--   $$v_i=-\frac{1}{M_{ii}}\sum_{j\ne i}M_{ij}w_j$$
--   so that the square in the completion of squares vanishes. Then $w^{\mathsf T}(\texttt{schurStep}\ M\ i)w=Q_i(w)=v^{\mathsf T}Mv\ge0$ because $M\succeq0$ — and this holds for every $w$, so the Schur complement is positive semidefinite by the quadratic-form characterisation, its symmetry being inherited from $M$.
--
--   This is the step that makes the elimination recursion work: it converts a question about an $n\times n$ matrix into the same question about an $(n-1)\times(n-1)$ matrix.
-- source:
--   Schur complement at a 1x1 pivot: the equivalence between semidefiniteness of a matrix and of its Schur complement. The induction step of the symmetric-elimination PSD oracle for the MAXCUT SDP separation problem.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurForm
import Definitions.Def_ModernConvex_SchurStep
import Theorems.Thm_ModernConvex_Relaxations_quadform_eq_schurForm
import Theorems.Thm_ModernConvex_Relaxations_schurForm_extendAt

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The Schur step, on the level of positive semidefiniteness.** At a positive pivot, `M` is
positive semidefinite exactly when its Schur complement at that pivot is. -/
theorem posSemidef_iff_schurStep {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : 0 < M i i) :
    M.PosSemidef ↔ (schurStep M i).PosSemidef := by sorry

end ModernConvex.Relaxations
