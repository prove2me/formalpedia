-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_integral_inner_convolution_eq_408915f
-- name    : FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:36.583155+00:00
-- url     : https://prove2.me/theorems/626b0c4e-7880-4c68-867f-13de65f493a0
-- title:
--   Symmetry of Mollification in the Inner-Product Pairing
-- statement:
--   This is the symmetry identity for convolution by a normalized even bump.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $E$ be a complete normed real inner-product space. Let $\varphi$ be a smooth bump centered at $0$. If $a:V\to E$ is integrable, and $b:V\to E$ is continuous and compactly supported, then
--
--   $$\int_V\left\langle(\varphi_{\mathrm{normed}}\ast a)(x),b(x)\right\に dm(x)
--   =\int_V\left\langle a(y),(\varphi_{\mathrm{normed}}\ast b)(y)\right\rangle\,dm(y).$$
--
--   The result transfers the mollifier between the two entries of the integrated inner product without reflecting the kernel.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L282-L350 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq`; the repository is private at upload time).

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
section Adjoint
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (φ : ContDiffBump (0 : V))

theorem FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_408915f {a b : V → E} (ha : Integrable a m) (hb : Continuous b)
    (hbc : HasCompactSupport b) :
    ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] a) x, b x⟫ ∂m =
      ∫ y, ⟪a y, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] b) y⟫ ∂m := by sorry
