-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_bound_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.slot_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:47.08573+00:00
-- url     : https://prove2.me/theorems/ce4763d5-d9d2-4ff2-890e-e23900cb107a
-- title:
--   Tensor Slot Bound From a Matrix Family Bound
-- statement:
--   This auxiliary lemma lifts a vector inequality to one tensor slot.
--
--   Let $H_i$ be a family of real $n\times n$ matrices satisfying, for every vector $v\in\mathbb R^n$,
--
--   $$
--   \sum_i\|H_i v\|^2\le 8\|v\|^2.
--   $$
--
--   Then for every order-$r$ coordinate tensor $T$ and every slot $s$,
--
--   $$
--   \sum_i\|H_i^{(s)}T\|^2\le 8\|T\|^2.
--   $$
--
--   This technical lifting result is used to control the slotwise terms in the drift estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma slot_bound (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
--       (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
--       (T : (Fin r → Fin n) → ℝ) (s : Fin r) :
--       ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 ≤
--         8 * ∑ J, T J ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Next: [`drift_expression_ge`](https://prove2.me/theorems/a395a5ad-1152-4611-ab50-eae8318965ce).
--
--   [Source excerpt, lines 45–49](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L45-L49) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L45-L134 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `_private.FunctionalInequalities.Analysis.Tensor.SlotAction.0.FunctionalInequalities.Analysis.CoordinateTensor.slot_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction

variable {n r : ℕ}

lemma FunctionalInequalities.Analysis.CoordinateTensor.slot_bound_readable (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T : (Fin r → Fin n) → ℝ) (s : Fin r) :
    ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 ≤
      8 * ∑ J, T J ^ 2 := by sorry
