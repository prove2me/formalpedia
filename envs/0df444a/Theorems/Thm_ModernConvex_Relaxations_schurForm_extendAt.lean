-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_schurForm_extendAt
-- name    : ModernConvex.Relaxations.schurForm_extendAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:24:29.031357+00:00
-- url     : https://prove2.me/theorems/f3d5c958-d3cf-4f57-b9ef-462bf3c68f3d
-- title:
--   The Schur form of the extended vector is the quadratic form of the Schur complement
-- statement:
--   **The Schur form is the quadratic form of the Schur complement.**
--
--   Let $M$ be a real symmetric matrix of order $n$ and $i$ an index. Write $\texttt{extendAt}\ i\ w$ for the vector on $\{1,\dots,n\}$ obtained from $w\in\mathbb R^{n-1}$ (indexed by the complement of $i$) by inserting $0$ at position $i$. Then
--   $$Q_i(\texttt{extendAt}\ i\ w)\;=\;w^{\mathsf T}\,(\texttt{schurStep}\ M\ i)\,w,$$
--   where $Q_i$ is the Schur form at $i$ and $\texttt{schurStep}\ M\ i$ is the Schur complement $M_{\ne i,\ne i}-M_{\ne i,i}M_{ii}^{-1}M_{i,\ne i}$.
--
--   Unwinding both sides: on the left, $Q_i$ is a sum over the index set $\{j\ne i\}$, whose summands involve only coordinates off $i$, so inserting a zero at $i$ changes nothing; on the right, expanding the Schur complement gives
--   $$\sum_{x,y}w_xM_{xy}w_y-M_{ii}^{-1}\Big(\sum_x w_xM_{xi}\Big)\Big(\sum_yM_{iy}w_y\Big),$$
--   and by symmetry $M_{xi}=M_{ix}$ the second factor pair is exactly $M_{ii}^{-1}\big(\sum_jM_{ij}w_j\big)^2$, matching the subtracted square in $Q_i$. The sums are reindexed between `Finset.univ.erase i` and the complement subtype by `Finset.sum_bij`.
--
--   This is the bridge that lets the PSD oracle recurse on matrices: it lets the Schur form (a form on $\mathbb R^n$ vanishing on the $i$-th coordinate) be replaced by the quadratic form of a genuine $(n-1)\times(n-1)$ matrix.
-- source:
--   Schur complement at a 1x1 pivot; the correspondence between the Schur form and the quadratic form of the Schur complement, for the recursive PSD oracle of the MAXCUT SDP.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurForm
import Definitions.Def_ModernConvex_SchurStep
import Theorems.Thm_ModernConvex_Relaxations_quadform_eq_schurForm
import Theorems.Thm_ModernConvex_Relaxations_sum_erase_eq_sum_subtype

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The Schur form of the extended vector is the quadratic form of the Schur step.** -/
theorem schurForm_extendAt {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (w : {j : Fin n // j ≠ i} → ℝ) :
    schurForm M i (extendAt i w) = w ⬝ᵥ (schurStep M i *ᵥ w) := by sorry

end ModernConvex.Relaxations
