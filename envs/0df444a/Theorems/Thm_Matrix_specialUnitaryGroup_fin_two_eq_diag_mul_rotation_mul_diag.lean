-- Prove2me | Theorems.Thm_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag
-- name    : Matrix.specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/031a8122-2ff5-58be-878d-90da3c7686fc
-- title:
--   Euler angle decomposition for SU(2)
-- statement:
--   Let $k$ be a $2\times 2$ matrix over $\mathbb{C}$, indexed by `Fin 2`, belonging to `Matrix.specialUnitaryGroup (Fin 2) ℂ`, i.e. $k$ is unitary ($k^{*}k = 1$ for the conjugate transpose) and has determinant $1$. The assertion is that there exist real numbers $a$, $b$, $c$ such that $k$ is equal to the product of three explicit matrices, in this order: the diagonal matrix with entries $e^{ia}$ and $e^{-ia}$ (formed from the coercion of $a$ to $\mathbb{C}$ times the complex unit), then the rotation matrix with rows $(\cos b, -\sin b)$ and $(\sin b, \cos b)$, its entries being the real cosine and sine coerced to $\mathbb{C}$, and then the diagonal matrix with entries $e^{ic}$ and $e^{-ic}$. All three factors are written as concrete $2\times 2$ matrix literals and the equality is an equality of matrices, not merely of the induced group elements.
--
--   This is the classical Euler angle decomposition $SU(2) = T\cdot SO(2)\cdot T$, with $T$ the diagonal circle; it is phrased purely in Mathlib terms. It is used to reduce invariance of a function on adelic $\mathrm{GL}(2)$ at a complex place under the diagonal torus and the real rotations to invariance under all of $SU(2)$, in [`AutomorphicForm.hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero`](thm.html#AutomorphicForm.hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag.lean

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag
    (k : Matrix (Fin 2) (Fin 2) ℂ) (hk : k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ a b c : ℝ,
      k = !![Complex.exp (a * Complex.I), 0; 0, Complex.exp (-(a * Complex.I))] *
            !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)] *
            !![Complex.exp (c * Complex.I), 0; 0, Complex.exp (-(c * Complex.I))] := by sorry
