-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_mapContinuousLinearEquiv_408915f
-- name    : FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapContinuousLinearEquiv_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:22.501296+00:00
-- url     : https://prove2.me/theorems/a5d1e75f-1f74-4b58-837c-e553e2d4c153
-- title:
--   Covariance Relaxation Under Linear Equivalence
-- statement:
--   This proves covariance-relaxation invariance under a continuous linear equivalence.
--
--   Let $V_1,V_2$ be complete real inner-product spaces with Borel measurable structures, let $\nu$ be a probability measure on $V_1$, let
--
--   $$
--   T:V_1\overset{\sim}{\longrightarrow}V_2
--   $$
--
--   be a continuous linear equivalence, and let $f\in L^2(T_\#\nu)$. Then
--
--   $$
--   \operatorname{relaxation}(T_\#\nu)(f)
--   =
--   \operatorname{relaxation}(\nu)(T^*f),
--   $$
--
--   where $T^*f$ denotes the pullback of $f$ through the induced $L^2$ equivalence, represented in Lean by `L2.ContinuousLinearEquiv.pullbackEquiv ν T`.
--
--   The statement expresses covariance-energy invariance under arbitrary invertible linear coordinate changes.
--
--   **Formalization Note** Finite-dimensionality and second-countability of the source are not required by the declaration; the target has the stated second-countability assumption.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/CovarianceGradient/LinearEquiv.lean#L147-L179 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv`, declaration `FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapContinuousLinearEquiv`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
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
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
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
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
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
universe u v
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
section Relaxation
variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
omit [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
omit [SecondCountableTopology V₁]

theorem FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapContinuousLinearEquiv_408915f (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    relaxation (Probability.mapContinuousLinearEquiv ν T) f = relaxation ν (L2.ContinuousLinearEquiv.pullbackEquiv ν T f) := by sorry
