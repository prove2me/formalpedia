-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_readable
-- name    : FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:27.194894+00:00
-- url     : https://prove2.me/theorems/341ba53c-b3cb-4ad0-873d-9d84885a6c75
-- title:
--   Trace Expansion for Four Matrix Factors
-- statement:
--   This is an algebraic expansion of the trace of a product of four real square matrices.
--
--   Let $n$ be a natural number and let $A,H,B,J$ be matrices in $M_n(\mathbb R)$. Then:
--
--   $$
--   \operatorname{tr}(AHBJ)=\sum_{a,b,c,d\in\operatorname{Fin}(n)}(A_{ab}B_{cd})(H_{bc}J_{da}).
--   $$
--
--   The Lean definition involved is `trace_mul_mul_mul_eq_sum_readable`. This identity is a reusable coordinate formula for trace quartics and does not require symmetry, invertibility, or positivity of any matrix.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem trace_mul_mul_mul_eq_sum {n : ℕ} (A H B J : Matrix (Fin n) (Fin n) ℝ) :
--       (A * H * B * J).trace =
--         ∑ q : Fin n × Fin n × Fin n × Fin n,
--           (A q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
--             (H q.2.1 q.2.2.1 * J q.2.2.2 q.1)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Trace/Algebra`](https://prove2.me/theorems/c47d46be-97ad-44e9-b115-414026fcb4ee).
--
--   Next: [`sum_matrix_product_entry_mul_eq_trace`](https://prove2.me/theorems/3c931abe-bff8-4022-a4df-7236818e79cd).
--
--   [Source excerpt, lines 88–92](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L88-L92) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L86-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`, declaration `FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra

theorem FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_readable {n : ℕ} (A H B J : Matrix (Fin n) (Fin n) ℝ) :
    (A * H * B * J).trace =
      ∑ q : Fin n × Fin n × Fin n × Fin n,
        (A q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
          (H q.2.1 q.2.2.1 * J q.2.2.2 q.1) := by sorry
