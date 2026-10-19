-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_residual_energy_bound_rounded
-- name    : HlawkaSchatten.DiagonalCutoff21.residual_energy_bound_rounded
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T08:19:27.177162+00:00
-- url     : https://prove2.me/theorems/34ad8b62-b3cd-4b9d-95b5-2dc7a3cf6c90
-- title:
--   Rational perturbation bound for the pair Hessian residual
-- statement:
--   For any finite index type $\iota$, real numbers $\rho,S\ge0$, and real families $a_i,b_i$ indexed by $\iota$, suppose $\sum_i a_i^2\le3S$ and $\sum_i b_i^2\le4\rho^2 S$. Then $\sum_i(a_i-b_i)^2\le(7/4+2\rho)^2S$. The assertion includes the empty index type, zero residuals and $\rho=0$. It is the algebraic energy estimate used after the two operator bounds in the pair-residual argument.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 6.2, equation (34). This helper isolates the finite-dimensional perturbation-energy estimate; its proof first obtains the slightly stronger coefficient 3+7*rho+4*rho^2.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

theorem HlawkaSchatten.DiagonalCutoff21.residual_energy_bound_rounded {ι : Type*} [Fintype ι]
    (rho S : ℝ) (a b : ι → ℝ)
    (hrho : 0 ≤ rho) (hS : 0 ≤ S)
    (ha : ∑ i, (a i) ^ 2 ≤ 3 * S)
    (hb : ∑ i, (b i) ^ 2 ≤ 4 * rho ^ 2 * S) :
    ∑ i, (a i - b i) ^ 2 ≤ (7 / 4 + 2 * rho) ^ 2 * S := by sorry
