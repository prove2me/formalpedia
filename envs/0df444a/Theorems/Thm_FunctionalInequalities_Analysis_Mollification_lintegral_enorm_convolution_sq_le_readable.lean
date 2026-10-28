-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_lintegral_enorm_convolution_sq_le_readable
-- name    : FunctionalInequalities.Analysis.Mollification.lintegral_enorm_convolution_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:36.695004+00:00
-- url     : https://prove2.me/theorems/63807bea-13bd-4a60-93ed-c5b5453cd20a
-- title:
--   Global $L^2$ Contraction Estimate for Mollification
-- statement:
--   This is the global squared extended-norm contraction estimate for a normalized mollifier.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, let $E$ be a normed real vector space, and let $\varphi$ be a smooth bump centered at $0$. If $f:V\to E$ is almost everywhere strongly measurable, then
--
--   $$\int_V\|(\varphi_{\mathrm{normed}}\ast f)(x)\|_e^2\,dm(x)
--   \le
--   \int_V\|f(x)\|_e^2\,dm(x).$$
--
--   Both integrals are lower integrals with values in $[0,\infty]$ (`ENNReal`). This is the measure-theoretic $L^2$ contraction property used in mollification arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Mollification`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_enorm_convolution_sq_le {f : V → E} (hf : AEStronglyMeasurable f m) :
--       ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m ≤
--         ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Supporting theorems: [`enorm_convolution_sq_le`](https://prove2.me/theorems/8688d530-bfa5-4460-868a-07eb55a8b66f).
--
--   Previous: [`enorm_convolution_sq_le`](https://prove2.me/theorems/8688d530-bfa5-4460-868a-07eb55a8b66f) · Next: [`tendsto_eLpNorm_convolution_sub_of_continuous`](https://prove2.me/theorems/a7a4227b-bc74-47d0-aecc-a60ae8cbf721).
--
--   [Source excerpt, lines 97–99](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L97-L99) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L96-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.lintegral_enorm_convolution_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))

theorem FunctionalInequalities.Analysis.Mollification.lintegral_enorm_convolution_sq_le_readable {f : V → E} (hf : AEStronglyMeasurable f m) :
    ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m ≤
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by sorry
