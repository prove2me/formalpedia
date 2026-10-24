-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_exists_lipschitzWith_of_eq_zero_outside_ball_408915f
-- name    : FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:53.569585+00:00
-- url     : https://prove2.me/theorems/80d1b855-edee-49ce-a3ce-69d559b47ae2
-- title:
--   Global Lipschitzness of Locally Lipschitz Compactly Supported Functions
-- statement:
--   This statement is the bounded-support Lipschitz principle.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $g:V\to\mathbb R$ be locally Lipschitz, and let $R\in\mathbb R$. Assume that $g$ vanishes outside the closed ball of radius $R$ centered at the origin, in the sense that
--
--   $$
--   R\leq\|x\|\quad\Longrightarrow\quad g(x)=0
--   $$
--
--   for every $x\in V$.
--
--   Then there exists some $K\in[0,\infty)$ such that $g$ is globally $K$-Lipschitz:
--
--   $$
--   \exists K\in[0,\infty),\qquad \operatorname{LipschitzWith}(K,g).
--   $$
--
--   The conclusion is existential and does not specify a particular Lipschitz constant. It supplies a standard reduction from locally Lipschitz functions with bounded support to globally Lipschitz tests.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L250-L300 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, declaration `FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball`; the repository is private at upload time).

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
section Reduction
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball_408915f {g : V → ℝ} {R : ℝ}
    (hg : LocallyLipschitz g) (hR : ∀ x, R ≤ ‖x‖ → g x = 0) :
    ∃ K : ℝ≥0, LipschitzWith K g := by sorry
