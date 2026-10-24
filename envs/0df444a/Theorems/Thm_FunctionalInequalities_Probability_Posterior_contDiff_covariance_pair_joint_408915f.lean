-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_covariance_pair_joint_408915f
-- name    : FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:29:55.675672+00:00
-- url     : https://prove2.me/theorems/053a2c6a-10a6-49e8-afb8-fb940d70e842
-- title:
--   Joint Smoothness of Posterior Covariances
-- statement:
--   This theorem states the joint $C^\infty$ regularity of posterior covariances of two linear statistics.
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with a measurable structure and its Borel structure. Let $\mu$ be a probability measure on $E$ such that its measure-theoretic support is compact. For arbitrary vectors $u,v\in E$, let $p=(c,Q)$ range over $E\times(E\to_L[\mathbb R]E)$, where $c\in E$ and $Q$ is a continuous linear operator from $E$ to $E$. The posterior measure at $p$ is the tilted measure
--   `(μ : Measure E).tilted (quadraticExponent c Q)`.
--
--   The covariance of the linear statistics $x\mapsto\langle u,x\rangle$ and $x\mapsto\langle v,x\rangle$ under this tilted measure is infinitely continuously differentiable jointly in $(c,Q)$:
--
--   $$
--   p\longmapsto \operatorname{Cov}_{\operatorname{tilted}(\mu,\,\operatorname{quadraticExponent}(c,Q))}\bigl(\langle u,X\rangle,\langle v,X\rangle\bigr)\quad\text{is }C^\infty.
--   $$
--
--   This is a technical regularity result that can be reused when differentiating posterior covariance expressions with respect to both the linear parameter and the quadratic operator parameter. It applies to arbitrary $u$ and $v$, including when $Q=0$, and does not require isotropy of the prior.
--
--   **Formalization Note** The conclusion is the Lean predicate `ContDiff ℝ ∞` on the product space $E\times(E\to_L[\mathbb R]E)$, with the operator space carrying its usual operator-norm structure. The covariance is formed with respect to the tilted measure and the statement does not assert any covariance identity beyond its joint smoothness.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean#L247-L274 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.JointRegularity`, declaration `FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint`; the repository is private at upload time).

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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
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
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
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
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities
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
section Moments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint_408915f (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (u v : E) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
        ((μ : Measure E).tilted (quadraticExponent p.1 p.2))) := by sorry
