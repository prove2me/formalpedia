-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_lintegral_enorm_convolution_sq_le_408915f
-- name    : FunctionalInequalities.Analysis.Mollification.lintegral_enorm_convolution_sq_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:36.114167+00:00
-- url     : https://prove2.me/theorems/13903976-9141-4b6d-ad4c-da6d5aadfb29
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L96-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.lintegral_enorm_convolution_sq_le`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Mollification.lintegral_enorm_convolution_sq_le_408915f {f : V → E} (hf : AEStronglyMeasurable f m) :
    ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m ≤
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by sorry
