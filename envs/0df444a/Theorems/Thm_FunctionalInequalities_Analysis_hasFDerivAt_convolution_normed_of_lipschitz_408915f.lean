-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_convolution_normed_of_lipschitz_408915f
-- name    : FunctionalInequalities.Analysis.hasFDerivAt_convolution_normed_of_lipschitz_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:47.907238+00:00
-- url     : https://prove2.me/theorems/149041df-36b4-4b43-a699-8628c1378f1f
-- title:
--   Derivative of a Mollified Lipschitz Map
-- statement:
--   This establishes the derivative formula for convolution with a normalized smooth bump.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel structure. Let $F:E\to E$ be Lipschitz with Lipschitz bound $G\in[0,\infty)$, let $\varphi$ be a smooth compactly supported bump centered at $0$, and let $x\in E$. Then the convolution of $F$ with the normalized bump $\varphi^{\mathrm{norm}}$ has a Fréchet derivative at $x$ given by the convolution of the almost-everywhere derivative of $F$:
--
--   $$
--   D\bigl(\varphi^{\mathrm{norm}}\!\ast F\bigr)(x)
--   =
--   \bigl(\varphi^{\mathrm{norm}}\!\ast DF\bigr)(x).
--   $$
--
--   In Lean, the convolution uses `ContinuousLinearMap.lsmul`, volume measure, and `fderiv ℝ F`. This is a supporting result for mollification identities.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L512-L557 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.hasFDerivAt_convolution_normed_of_lipschitz`; the repository is private at upload time).

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
section LipschitzConvolution
open MeasureTheory
open scoped Convolution
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]

theorem FunctionalInequalities.Analysis.hasFDerivAt_convolution_normed_of_lipschitz_408915f
    {F : E → E} {G : NNReal} (hF : LipschitzWith G F) (φ : ContDiffBump (0 : E)) (x : E) :
    HasFDerivAt (φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] F)
      ((φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        fderiv ℝ F) x) x := by sorry
