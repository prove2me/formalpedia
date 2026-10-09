-- Prove2me | Theorems.Thm_GaussianMatrix_specNorm_lipschitz
-- name    : GaussianMatrix.specNorm_lipschitz
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:28:59.832963+00:00
-- url     : https://prove2.me/theorems/88f6badf-eace-4dea-b00a-671d6383f023
-- title:
--   The spectral norm is $1$-Lipschitz for the Frobenius norm: $\big|\|A\|-\|B\|\big|\le\|A-B\|_F$
-- statement:
--   Let $A, B \in \mathbb{R}^{N\times n}$, let $\|M\| = \sup_{\|x\|_2 = 1}\|Mx\|_2$ denote the spectral ($\ell_2\to\ell_2$ operator) norm, i.e. the largest singular value, and let $\|M\|_F = \big(\sum_{i,j} M_{ij}^2\big)^{1/2}$ denote the Frobenius norm. Then
--   $$\big|\,\|A\| - \|B\|\,\big| \;\le\; \|A - B\|_F .$$
--
--   It follows from the reverse triangle inequality for the operator norm together with the comparison $\|M\| \le \|M\|_F$ (a consequence of the Cauchy–Schwarz inequality applied row by row). Its role is to make Gaussian concentration applicable to the largest singular value of a Gaussian matrix, giving $\mathbb{P}\{\|G\| \ge \sqrt N + \sqrt n + t\} \le e^{-t^2/2}$ when combined with Gordon's bound $\mathbb{E}\|G\| \le \sqrt N + \sqrt n$.
--
--   **Formalization Note.** `specNorm` is Mathlib's `Matrix.Norms.L2Operator` norm and `frobNorm A` is $\sqrt{\sum_{i,j} A_{ij}^2}$. The statement holds for all dimensions, including $N = 0$ or $n = 0$.
-- source:
--   standard fact: $|\,\|A\|-\|B\|\,|\le\|A-B\|_{op}\le\|A-B\|_F$ (reverse triangle inequality and operator norm $\le$ Frobenius norm); used in R. Vershynin, High-Dimensional Probability (Cambridge, 2018), proof of Corollary 7.3.3

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem specNorm_lipschitz {N n : ℕ} (A B : Matrix (Fin N) (Fin n) ℝ) :
    |specNorm A - specNorm B| ≤ frobNorm (A - B) := by sorry

end GaussianMatrix
