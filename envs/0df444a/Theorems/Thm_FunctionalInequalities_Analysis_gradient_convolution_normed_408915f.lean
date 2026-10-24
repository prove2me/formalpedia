-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_gradient_convolution_normed_408915f
-- name    : FunctionalInequalities.Analysis.gradient_convolution_normed_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:50.818515+00:00
-- url     : https://prove2.me/theorems/0f33fc36-7bc0-4fad-837e-f3738cafec00
-- title:
--   Gradient of a Mollified Scalar Function
-- statement:
--   This private lemma identifies the gradient of a mollified scalar function.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel structure. Let $U:E\to\mathbb R$ be $C^1$ and suppose that $\nabla U$ is Lipschitz with constant $G\in[0,\infty)$. For every smooth compactly supported bump $\varphi$,
--
--   $$
--   \nabla\bigl(\varphi^{\mathrm{norm}}\!\ast U\bigr)
--   =
--   \varphi^{\mathrm{norm}}\!\ast\nabla U.
--   $$
--
--   The convolution is with respect to volume measure and scalar multiplication is represented by `ContinuousLinearMap.lsmul`. This technical identity supports approximation by smooth convolutions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Hessian.lean#L85-L266 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Hessian`, declaration `_private.FunctionalInequalities.Analysis.Mollification.Hessian.0.FunctionalInequalities.Analysis.gradient_convolution_normed`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
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
open MeasureTheory Filter
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma FunctionalInequalities.Analysis.gradient_convolution_normed_408915f
    {U : E → ℝ} (hU : ContDiff ℝ 1 U)
    {G : NNReal} (hG : LipschitzWith G (gradient U))
    (φ : ContDiffBump (0 : E)) :
    gradient
        (convolution
          (φ.normed (volume : Measure E)) U
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E)) =
      convolution
        (φ.normed (volume : Measure E)) (gradient U)
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) := by sorry
