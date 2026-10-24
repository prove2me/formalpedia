-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_translateLaw_408915f
-- name    : FunctionalInequalities.Energy.CovarianceGradient.relaxation_translateLaw_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:00.040231+00:00
-- url     : https://prove2.me/theorems/eaa9792e-4cd5-4ef5-afb2-739efafa1b96
-- title:
--   Translation Invariance of Covariance Relaxation
-- statement:
--   This proves translation invariance of the covariance relaxation.
--
--   Let $V$ be a complete real inner-product space with its Borel measurable structure, let $\nu$ be a probability measure on $V$, let $c\in V$, and let $f\in L^2(\tau_c\#\nu)$, where $\tau_c(x)=c+x$. Then
--
--   $$
--   \operatorname{relaxation}(\tau_c\#\nu)(f)
--   =
--   \operatorname{relaxation}(\nu)(\tau_c^*f),
--   $$
--
--   where $\tau_c^*$ is the pullback isometry represented by `L2.Translation.pullbackEquiv ν c`.
--
--   The result formalizes independence of the covariance relaxation from the choice of affine origin.
--
--   **Formalization Note** No finite-dimensionality or second-countability assumption is required by the declaration.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/CovarianceGradient/Translation.lean#L125-L149 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.CovarianceGradient.Translation`, declaration `FunctionalInequalities.Energy.CovarianceGradient.relaxation_translateLaw`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
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
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
section Relaxation
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : ProbabilityMeasure V) (c : V)
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
omit [SecondCountableTopology V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.CovarianceGradient.relaxation_translateLaw_408915f (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    relaxation (Probability.translateLaw ν c) f = relaxation ν (L2.Translation.pullbackEquiv ν c f) := by sorry
