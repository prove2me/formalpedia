-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_tendsto_eLpNorm_convolution_sub_of_continuous_408915f
-- name    : FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:37.687131+00:00
-- url     : https://prove2.me/theorems/6ecd8ec4-6393-4ca4-97ca-8cc365131f2f
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L186-L233 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]
section Convergence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous_408915f {φ : ℕ → ContDiffBump (0 : V)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
      atTop (𝓝 0) := by sorry
