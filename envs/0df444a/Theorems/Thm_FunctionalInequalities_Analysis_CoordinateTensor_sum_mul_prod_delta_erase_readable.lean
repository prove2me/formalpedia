-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_sum_mul_prod_delta_erase_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:43.574448+00:00
-- url     : https://prove2.me/theorems/3d2d4761-884a-4e2c-9099-8cbf58b20f0b
-- title:
--   One-Slot Delta Collapse
-- statement:
--   This statement evaluates a finite sum constrained by Kronecker-delta factors.
--
--   Let $J:\operatorname{Fin}(r)\to\operatorname{Fin}(n)$, let $s\in\operatorname{Fin}(r)$, and let $f$ be a real-valued function on coordinate tensors. Then
--
--   $$
--   \sum_{J'}f(J')\prod_{s'\ne s}\delta_{J_{s'},J'_{s'}}
--   =\sum_{k\in\operatorname{Fin}(n)}f(J[s\mapsto k]).
--   $$
--
--   The product forces $J'$ to agree with $J$ outside slot $s$, leaving only the value in slot $s$ free. This finite combinatorial identity is used to collapse coordinate sums.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_mul_prod_delta_erase (J : Fin r → Fin n) (s : Fin r) (f : (Fin r → Fin n) → ℝ) :
--       ∑ J' : Fin r → Fin n, f J' * ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
--         ∑ k, f (Function.update J s k)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Previous: [`contDiffAt_energyForm`](https://prove2.me/theorems/3ecc6a67-dc0c-4de0-aced-f227c0a5133b) · Next: [`slot_derivative_sum`](https://prove2.me/theorems/da9c4569-cbdb-4d97-92a7-3f4b97b10178).
--
--   [Source excerpt, lines 95–97](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L95-L97) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L94-L154 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

variable {n r : ℕ}

theorem FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_readable (J : Fin r → Fin n) (s : Fin r) (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n, f J' * ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, f (Function.update J s k) := by sorry
