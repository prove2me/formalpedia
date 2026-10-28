-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_exists_norm_coordTensor_taylorTensor_le_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:59.801202+00:00
-- url     : https://prove2.me/theorems/f14f3dc2-aea1-4b21-93e6-8c5ccce91407
-- title:
--   Coordinate-Norm Bound for Taylor Tensors
-- statement:
--   This is a coordinate-norm continuity estimate for Taylor tensors.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $\mu$ be a probability measure on $E$, and assume that $e^{r\|x\|}$ is $\mu$-integrable for every $r\in\mathbb R$. For an integer $n$, an orthonormal basis $b$ indexed by $\operatorname{Fin}(n)$, and an order $d\in\mathbb N$, there exists $C\in\mathbb R$ such that every $f:E\to\mathbb R$ with $f\in L^2(\mu)$ satisfies
--
--   $$\|\operatorname{coordTensor}(b,T_d f)\|\le C\,(eLpNorm(f,2,\mu)).toReal.$$
--
--   The definition `coordTensor` uses the chosen basis and `taylorTensor` denotes $T_d f$. This statement transfers the fixed-order $L^2$ bound to the Hilbert–Schmidt norm of the coefficient array.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_norm_coordTensor_taylorTensor_le (μ : Measure E) [IsProbabilityMeasure μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {n : ℕ}
--       (b : OrthonormalBasis (Fin n) ℝ E) (d : ℕ) :
--       ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ →
--         ‖coordTensor b (taylorTensor μ f d)‖ ≤ C * (eLpNorm f 2 μ).toReal
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Definition modules: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`exists_norm_taylorTensor_le`](https://prove2.me/theorems/3b9f7ced-1180-435b-b7cb-81230ca3ce07), [`norm_coordTensor_le`](https://prove2.me/theorems/fe64a874-0aad-495c-87d8-2d0977852b27).
--
--   Previous: [`exists_norm_taylorTensor_le`](https://prove2.me/theorems/3b9f7ced-1180-435b-b7cb-81230ca3ce07) · Next: [`integrable_expTilt_of_memLp`](https://prove2.me/theorems/92338882-be7b-4eaa-bd08-2e7a5b6bd38c).
--
--   [Source excerpt, lines 559–563](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L559-L563) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L557-L574 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (d : ℕ) :
    ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ →
      ‖coordTensor b (taylorTensor μ f d)‖ ≤ C * (eLpNorm f 2 μ).toReal := by sorry
