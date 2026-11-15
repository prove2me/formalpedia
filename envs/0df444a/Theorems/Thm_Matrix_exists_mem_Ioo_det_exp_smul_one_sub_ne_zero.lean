-- Prove2me | Theorems.Thm_Matrix_exists_mem_Ioo_det_exp_smul_one_sub_ne_zero
-- name    : Matrix.exists_mem_Ioo_det_exp_smul_one_sub_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:36:40.539465+00:00
-- url     : https://prove2.me/theorems/59dd3375-f034-4367-b8b2-76e0ea6e696d
-- title:
--   Some point $e^{i\alpha}$, $0<\alpha<2\pi$, is not an eigenvalue of a complex matrix
-- statement:
--   Let $W$ be a square complex matrix, indexed by a finite type. Then there is $\alpha\in(0,2\pi)$ such that $\det(e^{i\alpha}I-W)\ne0$, i.e. $e^{i\alpha}$ is not an eigenvalue of $W$.
--
--   This gives a base angle avoiding the spectrum, as used when choosing a reference ray for angle or argument functions of unitary-type matrices.
--
--   Formalization Note: `exp ((α : ℂ) * I) • (1 : Matrix n n ℂ) - W` is $e^{i\alpha}I-W$.
-- source:
--   Standard

import Mathlib

namespace Matrix

open Complex Set

/-- For every square complex matrix `W` there is `α ∈ (0, 2π)` with
`det (exp (α i) • 1 - W) ≠ 0`. -/
theorem exists_mem_Ioo_det_exp_smul_one_sub_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) :
    ∃ α ∈ Ioo 0 (2 * Real.pi), (exp ((α : ℂ) * I) • (1 : Matrix n n ℂ) - W).det ≠ 0 := by
  sorry

end Matrix
