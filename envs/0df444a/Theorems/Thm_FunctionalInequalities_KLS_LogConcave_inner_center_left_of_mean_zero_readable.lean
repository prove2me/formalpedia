-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_inner_center_left_of_mean_zero_readable
-- name    : FunctionalInequalities.KLS.LogConcave.inner_center_left_of_mean_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:53.237986+00:00
-- url     : https://prove2.me/theorems/eeca0bb8-9f32-4e5c-ba1e-1f7ba9ea09b0
-- title:
--   Centering Does Not Change Pairings With Mean-Zero Classes
-- statement:
--   This theorem is a Hilbert-space identity for centered $L^2$ classes.
--
--   Let $\nu$ be any probability measure on a measurable space, and let $F,w\in L^2(\nu)$ with
--
--   $$
--   \operatorname{mean}_\nu(w)=0.
--   $$
--
--   Then
--
--   $$
--   \left\langle F-\operatorname{const}_\nu(\operatorname{mean}_\nu F),w\right\rangle
--   =\langle F,w\rangle.
--   $$
--
--   The left-hand side is `L2.center ν F`, and the constant class is `L2.const`. This elementary identity is useful when replacing a function by its centered version in variational estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_center_left_of_mean_zero
--       (ν : ProbabilityMeasure α) (F w : Lp ℝ 2 (ν : Measure α))
--       (hw : FunctionalInequalities.L2.mean ν w = 0) :
--       ⟪FunctionalInequalities.L2.center ν F, w⟫ = ⟪F, w⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/BrascampLieb`](https://prove2.me/theorems/ef0b3d78-2213-4c3c-ab7c-7dd44bfe1cfb).
--
--   Definition modules: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Previous: [`norm_sq_le_of_mem_closure_quadratic_bound`](https://prove2.me/theorems/db1af422-d999-42df-956f-acb4a17024e8) · Next: [`compact_pairing_identity`](https://prove2.me/theorems/77b2a911-3499-4ec7-80ff-b5c0181f947f).
--
--   [Source excerpt, lines 77–80](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BrascampLieb.lean#L77-L80) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/BrascampLieb.lean#L75-L93 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.BrascampLieb`, declaration `FunctionalInequalities.KLS.LogConcave.inner_center_left_of_mean_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb

open MeasureTheory Filter Topology Set InnerProductSpace
open scoped ContDiff RealInnerProductSpace
variable {α : Type*} [MeasurableSpace α]

theorem FunctionalInequalities.KLS.LogConcave.inner_center_left_of_mean_zero_readable
    (ν : ProbabilityMeasure α) (F w : Lp ℝ 2 (ν : Measure α))
    (hw : FunctionalInequalities.L2.mean ν w = 0) :
    ⟪FunctionalInequalities.L2.center ν F, w⟫ = ⟪F, w⟫ := by sorry
