-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_actOn_mul_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.actOn_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:47.248532+00:00
-- url     : https://prove2.me/theorems/cfa56bc5-17bf-4d9e-adde-cb98770df824
-- title:
--   Composition of Matrix Actions on One Tensor Slot
-- statement:
--   This statement identifies the action of a matrix product on one slot of a coordinate tensor.
--
--   Let $n,r\in\mathbb N$, let $M,N$ be real $n\times n$ matrices, let $s\in\operatorname{Fin}(r)$, and let $T:(\operatorname{Fin}(r)\to\operatorname{Fin}(n))\to\mathbb R$. Then
--
--   $$
--   (MN)^{(s)}T=M^{(s)}\bigl(N^{(s)}T\bigr),
--   $$
--
--   where $A^{(s)}T$ denotes the Lean operation `actOn A s T`. This algebraic identity is used to manipulate slotwise matrix actions on coordinate tensors.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem actOn_mul (M N : Matrix (Fin n) (Fin n) ℝ) (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
--       actOn (M * N) s T = actOn M s (actOn N s T)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Previous: [`drift_expression_ge`](https://prove2.me/theorems/a395a5ad-1152-4611-ab50-eae8318965ce) · Next: [`inner_actOn_left`](https://prove2.me/theorems/5abfdc6c-c268-4e15-8e06-33c59ea2d64e).
--
--   [Source excerpt, lines 315–316](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L315-L316) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L314-L349 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.actOn_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction

variable {n r : ℕ}

theorem FunctionalInequalities.Analysis.CoordinateTensor.actOn_mul_readable (M N : Matrix (Fin n) (Fin n) ℝ) (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
    actOn (M * N) s T = actOn M s (actOn N s T) := by sorry
