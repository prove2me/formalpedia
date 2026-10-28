-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_enorm_convolution_sq_le_readable
-- name    : FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:33.547185+00:00
-- url     : https://prove2.me/theorems/8688d530-bfa5-4460-868a-07eb55a8b66f
-- title:
--   Pointwise Squared Norm Bound for Mollification
-- statement:
--   This is the pointwise Cauchy–Schwarz estimate for convolution with a normalized smooth bump.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure on $V$, and let $E$ be a normed real vector space. Let $\varphi$ be a smooth bump centered at $0$, and let $f:V\to E$ be almost everywhere strongly measurable with respect to $m$. For every $x\in V$,
--
--   $$\left\|(\varphi_{\mathrm{normed}}\ast f)(x)\right\|_e^2
--   \le \int_V \operatorname{ofReal}(\varphi_{\mathrm{normed}}(t))\,\|f(x-t)\|_e^2\,dm(t).$$
--
--   The quantity $\|\cdot\|_e$ is the extended norm with values in $[0,\infty]$. This pointwise estimate is the local ingredient for $L^2$ contraction bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Mollification`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem enorm_convolution_sq_le {f : V → E} (hf : AEStronglyMeasurable f m) (x : V) :
--       ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ≤
--         ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Next: [`lintegral_enorm_convolution_sq_le`](https://prove2.me/theorems/63807bea-13bd-4a60-93ed-c5b5453cd20a).
--
--   [Source excerpt, lines 57–59](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L57-L59) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L56-L94 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))

theorem FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le_readable {f : V → E} (hf : AEStronglyMeasurable f m) (x : V) :
    ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ≤
      ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m := by sorry
