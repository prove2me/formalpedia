-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_bilinearIteratedFDerivTwo_posteriorExpectation_c_408915f
-- name    : FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:08:00.575843+00:00
-- url     : https://prove2.me/theorems/5cc5fb39-27bb-49ff-96ba-d45ea7a41cdb
-- title:
--   Posterior Expectation Hessian in the Linear Parameter
-- statement:
--   This is the $c$-Hessian formula for a compact posterior expectation.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $\mu$ be a compactly supported probability measure, and let $f:E\to\mathbb R$ be measurable and bounded on the support by $C\ge0$. For $c,h,k\in E$ and a continuous linear map $Q$, let $\nu=\mu.\operatorname{tilted}(\operatorname{quadraticExponent}(c,Q))$. Then
--
--   $$D_c^2\mathbb E_{\nu}[f](h,k)
--   =\operatorname{Cov}_{\nu}\bigl(f,x\mapsto\langle h,x\rangle\langle k,x\rangle\bigr)
--   -\left(\int\langle h,x\rangle\,d\nu\right)\operatorname{Cov}_{\nu}\bigl(f,\langle k,x\rangle\bigr)
--   -\left(\int\langle k,x\rangle\,d\nu\right)\operatorname{Cov}_{\nu}\bigl(f,\langle h,x\rangle\bigr).$$
--
--   Here `bilinearIteratedFDerivTwo` is the bilinear second derivative. The identity is the second-order deterministic ingredient for the posterior generator.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L138-L169 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, declaration `FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_408915f (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (h k : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c h k =
      covariance f (fun x => ⟪h, x⟫ * ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) *
          covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        (∫ x, ⟪k, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) *
          covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) := by sorry
