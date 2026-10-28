-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_hasDerivAt_energyForm_line_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_energyForm_line_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:53.511347+00:00
-- url     : https://prove2.me/theorems/7d3fc6e6-7635-41c8-9e97-877316e76ce3
-- title:
--   Directional Derivative of the Tensor Energy Form
-- statement:
--   This is a first-order directional derivative formula for the coordinate-tensor energy form.
--
--   Let $n,r\in\mathbb{N}$. Let $T,X:(\mathrm{Fin}\,r\to\mathrm{Fin}\,n)\to\mathbb{R}$, and let $H$ be a continuous linear map from $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$ to itself. Writing `energyForm` for the energy functional, `inner` for the tensor inner product, `stdMatrix H` for the standard matrix of $H$, and `actSum` for its induced tensor action, the derivative at $\varepsilon=0$ of
--
--   $$\varepsilon\mapsto \operatorname{energyForm}(1+\varepsilon H,T+\varepsilon X)$$
--
--   is
--
--   $$2\,\langle T,X\rangle-\left\langle T,\operatorname{actSum}(\operatorname{stdMatrix}(H),T)\right\rangle.$$
--
--   This technical line-derivative identity can be reused in first-order variations of tensor energy expressions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasDerivAt_energyForm_line (T : (Fin r → Fin n) → ℝ)
--       (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
--       HasDerivAt (fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X))
--         (2 * inner T X - inner T (actSum (stdMatrix H) T)) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Definition modules: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Supporting theorems: [`slot_derivative_sum`](https://prove2.me/theorems/da9c4569-cbdb-4d97-92a7-3f4b97b10178).
--
--   Previous: [`slot_derivative_sum`](https://prove2.me/theorems/da9c4569-cbdb-4d97-92a7-3f4b97b10178) · Next: [`sum_mul_prod_delta_erase_erase`](https://prove2.me/theorems/76502fa4-2d8b-4cb4-b4ba-234b9fc000dc).
--
--   [Source excerpt, lines 295–298](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L295-L298) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L293-L385 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_energyForm_line`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

variable {n r : ℕ}
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_energyForm_line_readable (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
    HasDerivAt (fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X))
      (2 * inner T X - inner T (actSum (stdMatrix H) T)) 0 := by sorry
