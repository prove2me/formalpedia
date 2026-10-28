-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_sum_two_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:44.498419+00:00
-- url     : https://prove2.me/theorems/e0d1f1e6-4957-4586-aef5-50f1a34f8224
-- title:
--   One-Slot Delta Collapse With Two Tensors
-- statement:
--   This auxiliary lemma evaluates a two-tensor coordinate sum with delta constraints.
--
--   For coordinate tensors $S,T$, a real matrix $M$, and order $r$ and dimension $n$, the sum
--
--   $$
--   \sum_{J,K}S_JT_K\sum_s
--   \left(\prod_{u\ne s}\delta_{J_u,K_u}\right)(-M_{J_sK_s})
--   $$
--
--   is equal to
--
--   $$
--   -\langle S,\Sigma_M T\rangle.
--   $$
--
--   Here $\Sigma_M T=\sum_sM^{(s)}T$. The lemma is an internal algebraic component of the energy-form derivative calculation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma slot_sum_two
--       (S T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
--       (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
--         S J * T K * (∑ s : Fin r,
--           (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
--             (-M (J s) (K s)))) =
--         -inner S (actSum M T)
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
--   Previous: [`fderiv_fderiv_apply_eq_deriv_deriv_line`](https://prove2.me/theorems/91499aa3-4a30-4b4f-af4c-05085add7997) · Next: [`two_slot_sum`](https://prove2.me/theorems/a6830ee8-1fb6-478d-9a58-968e1fda2c6d).
--
--   [Source excerpt, lines 679–685](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L679-L685) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L678-L736 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `_private.FunctionalInequalities.Analysis.Tensor.EnergyForm.0.FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

variable {n r : ℕ}

lemma FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two_readable
    (S T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
      S J * T K * (∑ s : Fin r,
        (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
          (-M (J s) (K s)))) =
      -inner S (actSum M T) := by sorry
