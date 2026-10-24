-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_domain_sequence_tendsto_408915f
-- name    : FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:53.710405+00:00
-- url     : https://prove2.me/theorems/c0c87e90-1886-46a2-87b5-5e70a06bb6ff
-- title:
--   Smooth Test Approximation In The Lipschitz Graph Domain
-- statement:
--   This theorem supplies a graph-norm approximating sequence for every smooth test under a local-density hypothesis.
--
--   Let $V$ be a finite-dimensional complete real inner-product normed space with its Borel measurable structure and second-countable topology. Let $\nu$ be a probability measure, let $m$ be an additive Haar measure, let $D$ be a local density for $(\nu,m)$, and let $f$ be a smooth-gradient test for $\nu$. Then there exists a sequence $(p_j)$ in the domain of the Lipschitz gradient operator such that
--
--   $$
--   \bigl(p_j,\operatorname{lipschitzOperator}(p_j)\bigr)
--   \longrightarrow
--   \bigl(f.\operatorname{toL2},
--   (\operatorname{MemLp.gradient}(f)).\operatorname{toLp}(\nabla f)\bigr)
--   $$
--
--   in the product topology as $j\to\infty$. Equivalently, the $L^2$ functions and their operator images converge simultaneously.
--
--   The declaration is `Test.exists_domain_sequence_tendsto`. The sequence consists of domain elements, and the gradient representative is placed in $L^2(\nu)$ using `toLp`; the statement is a convergence assertion rather than an equality at any finite index.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean#L179-L222 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Core`, declaration `FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
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
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Agreement
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure] (D : LocalDensity ν m)
open Energy.WeightedGradient Energy.Euclidean

theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto_408915f (f : Test ν) :
    ∃ p : ℕ → (lipschitzOperator ν m D).domain,
      Tendsto (fun j ↦ (((p j : (lipschitzOperator ν m D).domain) : Lp ℝ 2 (ν : Measure V)),
        lipschitzOperator ν m D (p j))) atTop
        (𝓝 (f.toL2, (Test.memLp_gradient ν f).toLp (gradient f.toFun))) := by sorry
