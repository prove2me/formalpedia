-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_lipschitzOnWith_mollify_ball_408915f
-- name    : FunctionalInequalities.Energy.lipschitzOnWith_mollify_ball_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:56.032403+00:00
-- url     : https://prove2.me/theorems/ede8bb36-20cb-4cbb-b406-8f408b707395
-- title:
--   Local Lipschitz Bound for Mollification on Balls
-- statement:
--   This statement gives the local Lipschitz stability of mollification under an additive Haar measure.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $m$ be an additive Haar measure on $V$. Let $R,\delta\in\mathbb R$ satisfy $0<R$. Let $c\in[0,\infty)$, let $g:V\to\mathbb R$ be continuous, and fix $x\in V$. Assume that $g$ is $c$-Lipschitz on the ball of radius $\delta+2R$ centered at $x$.
--
--   Then the mollification `mollify m R g` is $c$-Lipschitz on the ball of radius $\delta$ centered at $x$:
--
--   $$
--   \operatorname{LipschitzOnWith}(c,g,B(x,\delta+2R))
--   \;\Longrightarrow\;
--   \operatorname{LipschitzOnWith}(c,\operatorname{mollify}(m,R,g),B(x,\delta)).
--   $$
--
--   The result is a local recovery tool: the radius-$R$ mollifier requires control only on the enlarged ball of radius $\delta+2R$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L459-L493 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, declaration `FunctionalInequalities.Energy.lipschitzOnWith_mollify_ball`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
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
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section Mollification
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [CompleteSpace V] [SecondCountableTopology V]

theorem FunctionalInequalities.Energy.lipschitzOnWith_mollify_ball_408915f (m : Measure V) [m.IsAddHaarMeasure]
    {R δ : ℝ} (hR : 0 < R) {c : ℝ≥0} {g : V → ℝ} (hg : Continuous g) (x : V)
    (h : LipschitzOnWith c g (Metric.ball x (δ + 2 * R))) :
    LipschitzOnWith c (mollify m R g) (Metric.ball x δ) := by sorry
