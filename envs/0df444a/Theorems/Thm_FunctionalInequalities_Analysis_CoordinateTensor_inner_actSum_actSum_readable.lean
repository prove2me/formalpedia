-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_inner_actSum_actSum_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_actSum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:54.66218+00:00
-- url     : https://prove2.me/theorems/af677909-39f3-405f-9380-dc4ed282eb33
-- title:
--   Expansion of the Squared Slot-Sum Action
-- statement:
--   This statement expands the inner product of a coordinate tensor with its summed slot action.
--
--   Let $M$ be a symmetric real $n\times n$ matrix and let $T:(\operatorname{Fin}(r)\to\operatorname{Fin}(n))\to\mathbb R$. Then
--
--   $$
--   \begin{aligned}
--   \langle \Sigma_M T,\Sigma_M T\rangle
--   &=\sum_s\langle M^{(s)}T,M^{(s)}T\rangle\\
--   &\quad+\sum_s\sum_{t\in\operatorname{Fin}(r)\setminus\{s\}}
--   \langle T,M^{(s)}(M^{(t)}T)\rangle,
--   \end{aligned}
--   $$
--
--   where $\Sigma_M T=\sum_s M^{(s)}T$, implemented by `actSum`. This is the diagonal/off-diagonal decomposition used in the coordinate-tensor drift algebra.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_actSum_actSum (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (T : (Fin r → Fin n) → ℝ) :
--       inner (actSum M T) (actSum M T) =
--         ∑ s, inner (actOn M s T) (actOn M s T) +
--           ∑ s, ∑ t ∈ Finset.univ.erase s, inner T (actOn M s (actOn M t T))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Supporting theorems: [`inner_actOn_left`](https://prove2.me/theorems/5abfdc6c-c268-4e15-8e06-33c59ea2d64e).
--
--   Previous: [`inner_actOn_left`](https://prove2.me/theorems/5abfdc6c-c268-4e15-8e06-33c59ea2d64e).
--
--   [Source excerpt, lines 412–415](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L412-L415) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L411-L459 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_actSum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction

variable {n r : ℕ}

theorem FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_actSum_readable (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (T : (Fin r → Fin n) → ℝ) :
    inner (actSum M T) (actSum M T) =
      ∑ s, inner (actOn M s T) (actOn M s T) +
        ∑ s, ∑ t ∈ Finset.univ.erase s, inner T (actOn M s (actOn M t T)) := by sorry
