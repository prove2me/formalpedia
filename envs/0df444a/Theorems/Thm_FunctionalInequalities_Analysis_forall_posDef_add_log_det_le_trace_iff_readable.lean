-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_forall_posDef_add_log_det_le_trace_iff_readable
-- name    : FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:23.039276+00:00
-- url     : https://prove2.me/theorems/99f67c0b-fea3-4671-8e5b-e62a896aa733
-- title:
--   Log-Determinant Trace Characterization
-- statement:
--   This is a matrix characterization used in the weak Monge–Ampère route.
--
--   Let $A$ be a positive semidefinite real $n\times n$ matrix and let $b\in\mathbb R$. Then the following are equivalent:
--
--   1. for every positive definite matrix $J$,
--   $$b+\log\det J+n\le\operatorname{tr}(JA);$$
--   2. $A$ is positive definite and $e^b\le\det A$.
--
--   The statement is finite-dimensional and purely algebraic; it expresses the logarithmic determinant as an infimum of positive-definite trace functionals.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem forall_posDef_add_log_det_le_trace_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
--       (hA : A.PosSemidef) (b : ℝ) :
--       (∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef → b + Real.log J.det + n ≤ (J * A).trace) ↔
--         (A.PosDef ∧ Real.exp b ≤ A.det)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/LogDet`](https://prove2.me/theorems/4063692a-a203-477a-8815-ef391dc73f51).
--
--   Next: [`scalar_log_gap`](https://prove2.me/theorems/048f38d9-1535-47f8-a190-2a68f7a7a501).
--
--   [Source excerpt, lines 113–116](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L113-L116) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L110-L144 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.LogDet`, declaration `FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_LogDet

theorem FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff_readable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (b : ℝ) :
    (∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef → b + Real.log J.det + n ≤ (J * A).trace) ↔
      (A.PosDef ∧ Real.exp b ≤ A.det) := by sorry
