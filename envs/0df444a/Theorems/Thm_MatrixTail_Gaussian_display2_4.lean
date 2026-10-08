-- Prove2me | Theorems.Thm_MatrixTail_Gaussian_display2_4
-- name    : MatrixTail.Gaussian.display2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:11:04.567207+00:00
-- url     : https://prove2.me/theorems/8e6998d0-dedb-4784-90bf-14bf9b0b2758
-- title:
--   Display (2.4) — cosh(A) ≼ e^{A²/2} for every self-adjoint matrix A
-- statement:
--   For every self-adjoint complex $d\times d$ matrix $A$,
--   $$\cosh(A)\preccurlyeq e^{A^2/2},$$
--   where $\cosh(A)$ and $e^{A^2/2}$ are defined through the eigen-decomposition of $A$ and $\preccurlyeq$ is the semidefinite order.
--
--   This is the matrix version of the scalar inequality $\cosh x\le e^{x^2/2}$, transferred to matrices by the spectral calculus. It is what bounds the mgf of a Rademacher-modulated matrix in Lemma 4.3.
--
--   **Formalization Note** Both matrix functions are Mathlib's continuous functional calculus `cfc`; $A^2/2$ is the scalar multiple $\tfrac12\cdot A^2$.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 8, §2.4, display (2.4)

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Gaussian

/-- **Display (2.4)**, Tropp, arXiv:1004.4389v7, §2.4, p. 8: for each self-adjoint matrix `A`,
`cosh(A) ≼ e^{A²/2}`. (Cited in the proof of Lemma 4.3, p. 15: "the second relation is (2.4)".)

Formalization Note. Complex Hermitian `d × d` matrices; `cosh(A)` and `e^{A²/2}` are Mathlib's `cfc` of
`Real.cosh` and `Real.exp`; `≼` is the Loewner order `≤` under `MatrixOrder`; `A²/2` is written
`(1/2 : ℝ) • A ^ 2`. -/
theorem display2_4 {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    cfc Real.cosh A ≤ MatrixTail.Master.mexp ((1 / 2 : ℝ) • A ^ 2) := by sorry

end MatrixTail.Gaussian
