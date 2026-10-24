-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_sum_bilinearIteratedFDerivTwo_posteriorExpectation_c_408915f
-- name    : FunctionalInequalities.Probability.Posterior.sum_bilinearIteratedFDerivTwo_posteriorExpectation_c_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:08:04.861072+00:00
-- url     : https://prove2.me/theorems/0fb0b665-fb63-4912-8b1f-e5c16498fdec
-- title:
--   Trace of the Posterior Expectation Hessian
-- statement:
--   This is the trace formula for the posterior expectation Hessian against a symmetric operator.
--
--   Let $E$ be a finite-dimensional complete real inner-product space, let $\mu$ be compactly supported, and let $f$ be measurable and bounded on the support by $C\ge0$. Let $Q,M:E\to E$ be continuous linear maps, let $(b_i)$ be an orthonormal basis indexed by a finite type $\iota$, and assume $M$ is self-adjoint:
--
--   $$\langle Mu,v\rangle=\langle u,Mv\rangle.$$
--
--   For $\nu=\mu.\operatorname{tilted}(\operatorname{quadraticExponent}(c,Q))$ and $a=\operatorname{posteriorMean}(\mu,c,Q)$,
--
--   $$\sum_i D_c^2\mathbb E_{\nu}[f](M b_i,b_i)
--   =\operatorname{Cov}_{\nu}(f,x\mapsto\langle Mx,x\rangle)
--   -2\operatorname{Cov}_{\nu}(f,x\mapsto\langle Ma,x\rangle).$$
--
--   This converts the Hessian contribution into the covariance expression used in the generator calculation.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L211-L273 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, declaration `FunctionalInequalities.Probability.Posterior.sum_bilinearIteratedFDerivTwo_posteriorExpectation_c`; the repository is private at upload time).

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
section Mean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

theorem FunctionalInequalities.Probability.Posterior.sum_bilinearIteratedFDerivTwo_posteriorExpectation_c_408915f (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q M : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (hM : ∀ u v : E, ⟪M u, v⟫ = ⟪u, M v⟫) :
    (∑ i, bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c (M (b i)) (b i)) =
      covariance f (fun x => ⟪M x, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        2 * covariance f (fun x => ⟪M (posteriorMean μ c Q), x⟫)
          ((μ : Measure E).tilted (quadraticExponent c Q)) := by sorry
