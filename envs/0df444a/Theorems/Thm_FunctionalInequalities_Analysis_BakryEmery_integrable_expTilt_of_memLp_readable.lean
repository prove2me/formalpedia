-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_expTilt_of_memLp_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_expTilt_of_memLp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:07.029309+00:00
-- url     : https://prove2.me/theorems/92338882-be7b-4eaa-bd08-2e7a5b6bd38c
-- title:
--   Square-Integrable Functions Under Exponential Tilts
-- statement:
--   This theorem states that square-integrability is preserved as integrability under every exponential tilt.
--
--   Let $E$ be a real inner-product space, let $\mu$ be a finite measure on $E$ with all exponential moments, and let $G$ be a real normed space. If $g:E\to G$ belongs to $L^2(\mu)$, then for every $z\in E$,
--
--   $$g\in L^1\bigl(\operatorname{expTilt}(\mu,z)\bigr).$$
--
--   The Lean statement uses `MemLp g 2 μ` and concludes `Integrable g (expTilt μ z)`. This provides the integrability needed for tilt averages of square-integrable functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_expTilt_of_memLp
--       (μ : Measure E) [IsFiniteMeasure μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → G}
--       (hg : MemLp g 2 μ) (z : E) : Integrable g (expTilt μ z)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`integrable_exp_mul_norm_of_memLp`](https://prove2.me/theorems/151fb5bf-e4b4-47e5-9fbd-0c4e2f41eb82).
--
--   Previous: [`exists_norm_coordTensor_taylorTensor_le`](https://prove2.me/theorems/f14f3dc2-aea1-4b21-93e6-8c5ccce91407) · Next: [`taylorTensor_succ_of_eq_inner`](https://prove2.me/theorems/93f25a59-9d8a-4033-a79b-2ccbead0cd07).
--
--   [Source excerpt, lines 627–630](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L627-L630) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L625-L642 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_expTilt_of_memLp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E]
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_expTilt_of_memLp_readable
    (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → G}
    (hg : MemLp g 2 μ) (z : E) : Integrable g (expTilt μ z) := by sorry
