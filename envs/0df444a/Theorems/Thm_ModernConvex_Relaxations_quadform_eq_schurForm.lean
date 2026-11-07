-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_quadform_eq_schurForm
-- name    : ModernConvex.Relaxations.quadform_eq_schurForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:30:25.987746+00:00
-- url     : https://prove2.me/theorems/7be6f2a8-e8c3-4b87-9598-ce4f973883c8
-- title:
--   Completing the square: the quadratic form splits into a square and the Schur form
-- statement:
--   **Completing the square at a pivot.**
--
--   Let $M$ be a real symmetric matrix of order $n$, let $i$ be an index with $M_{ii}\ne0$, and let $v\in\mathbb R^n$. Then
--   $$v^{\mathsf T}Mv \;=\; M_{ii}\Big(v_i+\frac{1}{M_{ii}}\sum_{j\ne i}M_{ij}v_j\Big)^{2} \;+\; Q_i(v),$$
--   where
--   $$Q_i(v)=\sum_{j\ne i}\sum_{k\ne i}v_jv_kM_{jk}-\frac{1}{M_{ii}}\Big(\sum_{j\ne i}M_{ij}v_j\Big)^{2}$$
--   is the Schur form at $i$.
--
--   Equivalently: the part of the quadratic form that involves the $i$-th coordinate is a perfect square plus a constant, and $Q_i$ is the form on the remaining coordinates. Expanding both sides gives the elementary identity
--   $$M_{ii}v_i^2+2v_iP+Q, \qquad P=\sum_{j\ne i}M_{ij}v_j,\quad Q=\sum_{j,k\ne i}v_jv_kM_{jk},$$
--   for the left-hand side (splitting the double sum at $i$ and using symmetry $M_{ji}=M_{ij}$ on the two cross terms) and for the right-hand side (expanding the square and cancelling $M_{ii}^{-1}P^2$).
--
--   This is the algebraic heart of the symmetric-elimination PSD oracle: it converts a question about $M$ into a question about the smaller form $Q_i$, and it is what allows the $i$-th coordinate to be used either to cancel the square (producing a certificate of non-semidefiniteness) or to prove nonnegativity.
-- source:
--   Schur complement / symmetric Gaussian elimination; completing the square at a 1x1 pivot. Elimination step of the symmetric-elimination PSD test used for the separation oracle of Bubeck, arXiv:1405.4980v2, Thm 2.4.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurForm

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **Completing the square.** -/
theorem quadform_eq_schurForm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : M i i ≠ 0) (v : Fin n → ℝ) :
    v ⬝ᵥ (M *ᵥ v)
      = M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2
        + schurForm M i v := by sorry

end ModernConvex.Relaxations
