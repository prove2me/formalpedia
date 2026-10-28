-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_jordan_trace_domination_readable
-- name    : FunctionalInequalities.Analysis.jordan_trace_domination_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:51.075954+00:00
-- url     : https://prove2.me/theorems/a6423829-e14f-4879-bca7-f5ac02b2f042
-- title:
--   Jordan Trace Energy Domination
-- statement:
--   This statement gives trace-energy domination arising from a Jordan decomposition.
--
--   Let ι be a finite index type with decidable equality. Let P and N be positive semidefinite real matrices, and let H be symmetric. Then
--
--   $$\operatorname{tr}\bigl((P-N)H(P-N)H\bigr)
--   \leq \operatorname{tr}(PHPH)+\operatorname{tr}(NHNH).$$
--
--   No commutation between the matrices is assumed.
--
--   This pointwise matrix inequality is useful for extending estimates from positive semidefinite weights to arbitrary symmetric weights.
--
--   **Formalization Note** The result is purely finite-dimensional and uses ordinary real matrix multiplication and trace.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem jordan_trace_domination {P N H : Matrix ι ι ℝ}
--       (hP : P.PosSemidef) (hN : N.PosSemidef) (hH : H.IsSymm) :
--       ((P - N) * H * (P - N) * H).trace ≤
--         (P * H * P * H).trace + (N * H * N * H).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Trace/Energy`](https://prove2.me/theorems/3c755a85-5be5-4a52-9826-3a9afe9620f8).
--
--   Previous: [`trace_energy_nonneg`](https://prove2.me/theorems/1ddd2a2c-ff85-499e-a245-832c9fd056bb) · Next: [`letwin_trace_weighted_slices`](https://prove2.me/theorems/a517441b-78a2-4418-90ee-2e5a6b365cc7).
--
--   [Source excerpt, lines 117–120](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L117-L120) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L115-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Energy`, declaration `FunctionalInequalities.Analysis.jordan_trace_domination`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.jordan_trace_domination_readable {P N H : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) (hH : H.IsSymm) :
    ((P - N) * H * (P - N) * H).trace ≤
      (P * H * P * H).trace + (N * H * N * H).trace := by sorry
