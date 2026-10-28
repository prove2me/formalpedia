-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_sum_mul_prod_delta_erase_erase_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_erase_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:42.016581+00:00
-- url     : https://prove2.me/theorems/76502fa4-2d8b-4cb4-b4ba-234b9fc000dc
-- title:
--   Two-Slot Delta Collapse
-- statement:
--   This statement evaluates delta constraints leaving two tensor slots free.
--
--   Let $J:\operatorname{Fin}(r)\to\operatorname{Fin}(n)$, let distinct slots $s,t\in\operatorname{Fin}(r)$ satisfy $s\ne t$, and let $f$ be real-valued on coordinate tensors. Then
--
--   $$
--   \sum_{J'}f(J')\prod_{u\notin\{s,t\}}\delta_{J_u,J'_u}
--   =\sum_{k,l\in\operatorname{Fin}(n)}f(J[s\mapsto k][t\mapsto l]).
--   $$
--
--   The identity is a finite reindexing tool for sums with all coordinates fixed except two.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_mul_prod_delta_erase_erase (J : Fin r → Fin n) {s t : Fin r} (hst : s ≠ t)
--       (f : (Fin r → Fin n) → ℝ) :
--       ∑ J' : Fin r → Fin n, f J' *
--           ∏ s' ∈ (Finset.univ.erase s).erase t, (if J s' = J' s' then (1 : ℝ) else 0) =
--         ∑ k, ∑ l, f (Function.update (Function.update J s k) t l)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Previous: [`hasDerivAt_energyForm_line`](https://prove2.me/theorems/7d3fc6e6-7635-41c8-9e97-877316e76ce3) · Next: [`fderiv_fderiv_apply_eq_deriv_deriv_line`](https://prove2.me/theorems/91499aa3-4a30-4b4f-af4c-05085add7997).
--
--   [Source excerpt, lines 496–500](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L496-L500) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L494-L586 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_erase`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

variable {n r : ℕ}

theorem FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_erase_readable (J : Fin r → Fin n) {s t : Fin r} (hst : s ≠ t)
    (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n, f J' *
        ∏ s' ∈ (Finset.univ.erase s).erase t, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, ∑ l, f (Function.update (Function.update J s k) t l) := by sorry
