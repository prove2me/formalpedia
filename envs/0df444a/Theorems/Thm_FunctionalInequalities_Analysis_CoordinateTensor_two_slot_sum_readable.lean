-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_two_slot_sum_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.two_slot_sum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:58.363806+00:00
-- url     : https://prove2.me/theorems/a6830ee8-1fb6-478d-9a58-968e1fda2c6d
-- title:
--   Two-Slot Mixed Delta Collapse
-- statement:
--   This auxiliary lemma evaluates the mixed two-slot term arising from two matrix factors.
--
--   For a coordinate tensor $T$ and a real matrix $M$, the sum with two distinct slots and delta constraints equals
--
--   $$
--   \sum_s\sum_{u\ne s}
--   \left\langle T,M^{(s)}(M^{(u)}T)\right\rangle.
--   $$
--
--   More explicitly, the left side is the finite sum over $J,K$ and $s,u$ whose factors are
--   $T_JT_K$, the product of deltas outside $s$ and $u$, and $(-M_{J_uK_u})(-M_{J_sK_s})$. This is an internal identity used in the second derivative of the energy form.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma two_slot_sum (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
--       (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n, T J * T K *
--         (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
--           (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
--             (-M (J u) (K u))) * (-M (J s) (K s)))) =
--         ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, inner T (actOn M s (actOn M u T))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Definition modules: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Supporting theorems: [`sum_mul_prod_delta_erase_erase`](https://prove2.me/theorems/76502fa4-2d8b-4cb4-b4ba-234b9fc000dc).
--
--   Previous: [`slot_sum_two`](https://prove2.me/theorems/e0d1f1e6-4957-4586-aef5-50f1a34f8224) · Next: [`deriv_deriv_energyForm_line`](https://prove2.me/theorems/8ec8d6e9-231a-4f63-b067-a5beeb835aaf).
--
--   [Source excerpt, lines 759–764](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L759-L764) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L758-L847 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `_private.FunctionalInequalities.Analysis.Tensor.EnergyForm.0.FunctionalInequalities.Analysis.CoordinateTensor.two_slot_sum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

variable {n r : ℕ}

lemma FunctionalInequalities.Analysis.CoordinateTensor.two_slot_sum_readable (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n, T J * T K *
      (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
        (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
          (-M (J u) (K u))) * (-M (J s) (K s)))) =
      ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, inner T (actOn M s (actOn M u T)) := by sorry
