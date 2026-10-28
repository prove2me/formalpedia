-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_letwin_trace_weighted_slices_readable
-- name    : FunctionalInequalities.Analysis.letwin_trace_weighted_slices_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:40.09678+00:00
-- url     : https://prove2.me/theorems/a517441b-78a2-4418-90ee-2e5a6b365cc7
-- title:
--   Weighted Matrix-Slice Trace Expansion
-- statement:
--   This is a finite matrix expansion identity.
--
--   For real $n\times n$ matrices $P,A,C$ and a family of matrices $V_a$, one has
--
--   $$
--   \sum_k\operatorname{tr}\left(A\left(\sum_aP_{ka}V_a\right)C\left(\sum_bP_{kb}V_b\right)\right)
--   =
--   \sum_{a,b}(P^{\mathsf T}P)_{ab}\operatorname{tr}(AV_aCV_b).
--   $$
--
--   The statement is purely algebraic and is used to rewrite a sum of traces of weighted matrix slices.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma letwin_trace_weighted_slices {n : ℕ}
--       (P A C : Matrix (Fin n) (Fin n) ℝ)
--       (V : Fin n → Matrix (Fin n) (Fin n) ℝ) :
--       (∑ k, (A * (∑ a, P k a • V a) * C *
--         (∑ b, P k b • V b)).trace) =
--         ∑ a, ∑ b, (Pᵀ * P) a b * (A * V a * C * V b).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Trace/Energy`](https://prove2.me/theorems/3c755a85-5be5-4a52-9826-3a9afe9620f8).
--
--   Previous: [`jordan_trace_domination`](https://prove2.me/theorems/a6423829-e14f-4879-bca7-f5ac02b2f042) · Next: [`letwin_tensor_trace_identity`](https://prove2.me/theorems/fae84bdf-a098-4054-b01e-b2eb219e86ec).
--
--   [Source excerpt, lines 243–248](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L243-L248) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L243-L290 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Energy`, declaration `_private.FunctionalInequalities.Analysis.Matrix.Trace.Energy.0.FunctionalInequalities.Analysis.letwin_trace_weighted_slices`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy

open Matrix

lemma FunctionalInequalities.Analysis.letwin_trace_weighted_slices_readable {n : ℕ}
    (P A C : Matrix (Fin n) (Fin n) ℝ)
    (V : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ k, (A * (∑ a, P k a • V a) * C *
      (∑ b, P k b • V b)).trace) =
      ∑ a, ∑ b, (Pᵀ * P) a b * (A * V a * C * V b).trace := by sorry
