-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_inner_actOn_left_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_left_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:42.722408+00:00
-- url     : https://prove2.me/theorems/5abfdc6c-c268-4e15-8e06-33c59ea2d64e
-- title:
--   Self-Adjointness of a Symmetric Slot Action
-- statement:
--   This statement proves self-adjointness of the action of a symmetric matrix on one tensor slot.
--
--   Let $M$ be a real $n\times n$ matrix satisfying $M^\mathsf T=M$. For $s\in\operatorname{Fin}(r)$ and coordinate tensors $T,S:(\operatorname{Fin}(r)\to\operatorname{Fin}(n))\to\mathbb R$, one has
--
--   $$
--   \langle M^{(s)}T,S\rangle
--   =\langle T,M^{(s)}S\rangle.
--   $$
--
--   Here the inner product is the finite coordinate-tensor inner product and $M^{(s)}$ is `actOn M s`. The identity is used to move symmetric slot actions between factors in tensor estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_actOn_left (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (s : Fin r)
--       (T S : (Fin r → Fin n) → ℝ) : inner (actOn M s T) S = inner T (actOn M s S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Previous: [`actOn_mul`](https://prove2.me/theorems/cfa56bc5-17bf-4d9e-adde-cb98770df824) · Next: [`inner_actSum_actSum`](https://prove2.me/theorems/af677909-39f3-405f-9380-dc4ed282eb33).
--
--   [Source excerpt, lines 352–353](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L352-L353) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L351-L403 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_left`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction

variable {n r : ℕ}

theorem FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_left_readable (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (s : Fin r)
    (T S : (Fin r → Fin n) → ℝ) : inner (actOn M s T) S = inner T (actOn M s S) := by sorry
