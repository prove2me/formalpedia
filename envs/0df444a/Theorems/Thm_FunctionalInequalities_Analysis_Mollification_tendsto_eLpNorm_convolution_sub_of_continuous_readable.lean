-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_tendsto_eLpNorm_convolution_sub_of_continuous_readable
-- name    : FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:35.714067+00:00
-- url     : https://prove2.me/theorems/a7a4227b-bc74-47d0-aecc-a60ae8cbf721
-- title:
--   Mollification Convergence for Compactly Supported Continuous Functions
-- statement:
--   This establishes $L^2$ convergence of mollifications in the continuous compactly supported case.
--
--   Let $V$ be a finite-dimensional real inner-product space with an additive Haar measure $m$, let $E$ be a complete normed real vector space, and let $(\varphi_n)_{n\in\mathbb{N}}$ be smooth bumps centered at $0$. Assume their outer radii satisfy
--
--   $$r_{\mathrm{out}}(\varphi_n)\longrightarrow 0.$$
--
--   For every continuous compactly supported function $f:V\to E$,
--
--   $$eLpNorm(\varphi_{n,\mathrm{normed}}\ast f-f,2,m)\longrightarrow 0.$$
--
--   The convergence is in the extended $L^2$ norm, whose values lie in $[0,\infty]$. This is the basic approximation result used to extend mollification convergence from regular functions to general $L^2$ functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Mollification`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_eLpNorm_convolution_sub_of_continuous {φ : ℕ → ContDiffBump (0 : V)}
--       (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → E} (hf : Continuous f)
--       (hfc : HasCompactSupport f) :
--       Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
--         atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Previous: [`lintegral_enorm_convolution_sq_le`](https://prove2.me/theorems/63807bea-13bd-4a60-93ed-c5b5453cd20a) · Next: [`tendsto_eLpNorm_convolution_sub`](https://prove2.me/theorems/3e5007ce-6906-4a04-82a9-55a0bdd821b3).
--
--   [Source excerpt, lines 188–192](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L188-L192) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L186-L233 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous_readable {φ : ℕ → ContDiffBump (0 : V)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
      atTop (𝓝 0) := by sorry
