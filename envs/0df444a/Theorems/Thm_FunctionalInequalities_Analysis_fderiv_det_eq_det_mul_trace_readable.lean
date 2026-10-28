-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_fderiv_det_eq_det_mul_trace_readable
-- name    : FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:14.404414+00:00
-- url     : https://prove2.me/theorems/7b944e90-ac35-4a2d-a68e-0c989cf61604
-- title:
--   Jacobi Formula for the Determinant
-- statement:
--   This is Jacobi’s formula for a real square matrix.
--
--   Let $M,N$ be matrices indexed by a finite type, and assume $\det M$ is a unit, equivalently that $M$ is invertible. Then the Fréchet derivative of the determinant at $M$ in direction $N$ is
--
--   $$
--   D(\det)_M[N]=\det(M)\,\operatorname{tr}(M^{-1}N).
--   $$
--
--   The result is a finite-dimensional algebraic identity and imposes no symmetry, positivity, or regularity assumptions on $M$ or $N$. In Lean it is expressed by `fderiv ℝ Matrix.det M N` and matrix multiplication and trace.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_det_eq_det_mul_trace (M N : Matrix ι ι ℝ) (hM : IsUnit M.det) :
--       fderiv ℝ Matrix.det M N = M.det * Matrix.trace (M⁻¹ * N)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/DeterminantDerivative`](https://prove2.me/theorems/46a9a92e-982e-4a04-af01-9373c2e17873).
--
--   [Source excerpt, lines 46–47](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean#L46-L47) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean#L45-L68 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.DeterminantDerivative`, declaration `FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_readable (M N : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    fderiv ℝ Matrix.det M N = M.det * Matrix.trace (M⁻¹ * N) := by sorry
