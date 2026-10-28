-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_derivative_sum_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.slot_derivative_sum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:55.845533+00:00
-- url     : https://prove2.me/theorems/da9c4569-cbdb-4d97-92a7-3f4b97b10178
-- title:
--   Derivative Sum for One-Slot Energy Terms
-- statement:
--   This auxiliary lemma evaluates the first-order matrix contribution in a coordinate-tensor energy calculation.
--
--   For an order-$r$ coordinate tensor $T$ and a real matrix $M$, the finite sum
--
--   $$
--   \sum_{J,K}T_JT_K\sum_s
--   \left(\prod_{u\ne s}\delta_{J_u,K_u}\right)(-M_{J_sK_s})
--   $$
--
--   equals
--
--   $$
--   -\langle T,\Sigma_M T\rangle.
--   $$
--
--   The result is a purely finite algebraic identity used internally in differentiating the energy form.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma slot_derivative_sum
--       (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
--       (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
--         T J * T K * (∑ s : Fin r,
--           (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
--             (-M (J s) (K s)))) =
--         -inner T (actSum M T)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Definition modules: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Supporting theorems: [`sum_mul_prod_delta_erase`](https://prove2.me/theorems/3d2d4761-884a-4e2c-9099-8cbf58b20f0b).
--
--   Previous: [`sum_mul_prod_delta_erase`](https://prove2.me/theorems/3d2d4761-884a-4e2c-9099-8cbf58b20f0b) · Next: [`hasDerivAt_energyForm_line`](https://prove2.me/theorems/7d3fc6e6-7635-41c8-9e97-877316e76ce3).
--
--   [Source excerpt, lines 233–239](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L233-L239) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L233-L291 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `_private.FunctionalInequalities.Analysis.Tensor.EnergyForm.0.FunctionalInequalities.Analysis.CoordinateTensor.slot_derivative_sum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

variable {n r : ℕ}

lemma FunctionalInequalities.Analysis.CoordinateTensor.slot_derivative_sum_readable
    (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
      T J * T K * (∑ s : Fin r,
        (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
          (-M (J s) (K s)))) =
      -inner T (actSum M T) := by sorry
