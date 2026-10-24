-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_tendsto_eLpNorm_convolution_sub_408915f
-- name    : FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:38.863445+00:00
-- url     : https://prove2.me/theorems/d089ca99-3ba2-46c7-8b43-b281ea0b3200
-- title:
--   Mollification Convergence for $L^2$ Functions
-- statement:
--   This establishes $L^2$ convergence of mollifications for arbitrary $L^2$ functions.
--
--   Let $V$ be a finite-dimensional real inner-product space with an additive Haar measure $m$, let $E$ be a complete normed real vector space, and let $(\varphi_n)_{n\in\mathbb{N}}$ be smooth bumps centered at $0$. Assume
--
--   $$r_{\mathrm{out}}(\varphi_n)\longrightarrow 0.$$
--
--   If $f:V\to E$ satisfies `MemLp f 2 m`, then
--
--   $$eLpNorm(\varphi_{n,\mathrm{normed}}\ast f-f,2,m)\longrightarrow 0.$$
--
--   This is an $L^2$-approximation theorem for mollification and uses the extended norm convention of `eLpNorm`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L235-L273 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_408915f {φ : ℕ → ContDiffBump (0 : V)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → E} (hf : MemLp f 2 m) :
    Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
      atTop (𝓝 0) := by sorry
