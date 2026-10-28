-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_log_det_add_frobenius_sq_le_readable
-- name    : FunctionalInequalities.Analysis.log_det_add_frobenius_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:12.545989+00:00
-- url     : https://prove2.me/theorems/42e7e2e1-c8f2-4cb8-b154-81b11d6da306
-- title:
--   Quantitative Concavity of Log Determinant
-- statement:
--   This is the quantitative matrix log-determinant inequality cited in the module documentation in connection with Lemma 4.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $A,B$ be real $n\times n$ matrices and $K\in\mathbb R$. Assume:
--
--   1. $A$ and $B$ are positive definite.
--   2. $K I-A$ is positive semidefinite.
--   3. $K I-B$ is positive semidefinite.
--
--   Then
--
--   $$\log\det B+\frac{\|B-A\|_F^2}{2K^2}
--   \le \log\det A+\operatorname{tr}\!\left(A^{-1}(B-A)\right),$$
--
--   where $\|B-A\|_F^2=\sum_{i,j}(B_{ij}-A_{ij})^2$. The declaration `log_det_add_frobenius_sq_le_readable` is a finite-dimensional matrix inequality; positivity and the upper bounds are expressed through `PosDef` and `PosSemidef`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem log_det_add_frobenius_sq_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
--       (hA : A.PosDef) (hB : B.PosDef) (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
--       (hBK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - B).PosSemidef) :
--       Real.log B.det + (∑ i, ∑ j, (B - A) i j ^ 2) / (2 * K ^ 2) ≤
--         Real.log A.det + (A⁻¹ * (B - A)).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/LogDet`](https://prove2.me/theorems/4063692a-a203-477a-8815-ef391dc73f51).
--
--   Supporting theorems: [`scalar_log_gap`](https://prove2.me/theorems/048f38d9-1535-47f8-a190-2a68f7a7a501).
--
--   Previous: [`scalar_log_gap`](https://prove2.me/theorems/048f38d9-1535-47f8-a190-2a68f7a7a501).
--
--   [Source excerpt, lines 347–351](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L347-L351) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L344-L484 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.LogDet`, declaration `FunctionalInequalities.Analysis.log_det_add_frobenius_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_LogDet

set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.log_det_add_frobenius_sq_le_readable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hBK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - B).PosSemidef) :
    Real.log B.det + (∑ i, ∑ j, (B - A) i j ^ 2) / (2 * K ^ 2) ≤
      Real.log A.det + (A⁻¹ * (B - A)).trace := by sorry
