-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_eq_ofLinearPMap_408915f
-- name    : FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:18.835595+00:00
-- url     : https://prove2.me/theorems/66613306-ab80-474d-81fb-bc2dd53a0b4e
-- title:
--   Covariance Relaxation as a Weighted-Gradient Relaxation
-- statement:
--   This identifies the covariance relaxation with a sequential pre-energy relaxation.
--
--   Let $V$ be a finite-dimensional complete real inner-product space with its Borel measurable structure, let $\nu$ be a probability measure on $V$, let $m$ be an additive Haar measure, and let $B:V\to V$ be continuous linear. Assume:
--
--   1. $\nu$ is absolutely continuous with respect to $m$;
--   2. the frontier of the support of $\nu$ has $\nu$-measure zero;
--   3. for every $v\in V$,
--
--   $$
--   \langle\operatorname{Cov}(\nu)v,v\rangle=\|Bv\|^2.
--   $$
--
--   Then
--
--   $$
--   \operatorname{relaxation}(\nu)
--   =
--   \operatorname{sequentialRelaxation}\bigl(\operatorname{PreEnergy.ofLinearPMap}(\operatorname{WeightedGradient.operator}(\nu,B))\bigr).
--   $$
--
--   The result is the formal bridge between covariance energy and the squared-norm energy of a weighted gradient operator.
--
--   **Formalization Note** The equality is between extended nonnegative-valued functionals; the absolute-continuity and support-frontier hypotheses are explicit.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/WeightedGradient/Basic.lean#L347-L384 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.WeightedGradient.Basic`, declaration `FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
section Operator
variable [MeasurableSpace V] (ν : ProbabilityMeasure V) (B : V →L[ℝ] V)
variable [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {m : Measure V} [m.IsAddHaarMeasure]
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
open WeightedGradient

theorem FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap_408915f (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) :
    relaxation ν =
      (PreEnergy.ofLinearPMap (operator ν B hac)).sequentialRelaxation := by sorry
