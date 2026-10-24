-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_enorm_convolution_sq_le_408915f
-- name    : FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:36.410972+00:00
-- url     : https://prove2.me/theorems/6c0fb217-4390-4c48-930b-7b4607dc87a6
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L56-L94 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le`; the repository is private at upload time).

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
section Contraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))

theorem FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le_408915f {f : V → E} (hf : AEStronglyMeasurable f m) (x : V) :
    ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ≤
      ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m := by sorry
