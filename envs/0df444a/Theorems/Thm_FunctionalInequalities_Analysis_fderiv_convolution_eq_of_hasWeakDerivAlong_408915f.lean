-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_fderiv_convolution_eq_of_hasWeakDerivAlong_408915f
-- name    : FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:55.718429+00:00
-- url     : https://prove2.me/theorems/bc305ed3-6c0d-413f-b442-3fd1fb548bf5
-- title:
--   Mollification Commutes with Weak Directional Differentiation
-- statement:
--   This is the generic weak-derivative identity for mollification.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $f,g:E\to\mathbb{R}$ and $v\in E$, and assume `HasWeakDerivAlong f g v`. Let $\varphi$ be a smooth compactly supported bump centered at $0$, and let $x\in E$. Then
--
--   $$D_v\bigl((\varphi_{\mathrm{normed}}\ast f)(x)\bigr)
--   =(\varphi_{\mathrm{normed}}\ast g)(x).$$
--
--   In Lean, the directional derivative is `fderiv ℝ (...) x v`, and the convolution uses volume measure. This identifies the classical derivative of the mollified function with the mollification of the weak derivative.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean#L23-L83 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Mollification`, declaration `FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
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
open MeasureTheory
open scoped ContDiff
section LW3B1WeakDerivativeMollification
open MeasureTheory Set Filter
open scoped Topology Convolution
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
      convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by sorry
