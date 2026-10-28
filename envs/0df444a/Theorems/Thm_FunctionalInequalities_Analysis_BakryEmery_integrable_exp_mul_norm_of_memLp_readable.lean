-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_exp_mul_norm_of_memLp_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:57.822524+00:00
-- url     : https://prove2.me/theorems/151fb5bf-e4b4-47e5-9fbd-0c4e2f41eb82
-- title:
--   Exponential Weighted Integrability of an $L^2$ Function
-- statement:
--   This is an integrability lemma for square-integrable functions under exponential moment assumptions.
--
--   Let $E$ be a normed real space with a measurable Borel structure, let $\mu$ be a finite measure, and assume that every exponential norm weight is integrable:
--
--   $$
--   \forall s\in\mathbb R,
--   \quad \int e^{s\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   If $f:E\to\mathbb R$ belongs to $L^2(\mu)$ and $r\in\mathbb R$, then
--
--   $$
--   \int e^{r\|x\|}\,\|f(x)\|\,d\mu(x)<\infty.
--   $$
--
--   The hypothesis is `MemLp f 2 μ`; no inner-product, finite-dimensional, or completeness assumption is required. This result is used to control weighted tilt integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_exp_mul_norm_of_memLp (μ : Measure E) [IsFiniteMeasure μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ)
--       (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖) * ‖f x‖) μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Previous: [`iteratedFDeriv_integral_exp_inner_smul`](https://prove2.me/theorems/5c6a3c00-e76c-4094-bd9b-db3f77cc3227) · Next: [`contDiff_tiltAverage_of_memLp`](https://prove2.me/theorems/48443cd3-183a-49bc-b5a9-dc2888cd75a0).
--
--   [Source excerpt, lines 253–255](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L253-L255) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L250-L277 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_readable (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ)
    (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖) * ‖f x‖) μ := by sorry
