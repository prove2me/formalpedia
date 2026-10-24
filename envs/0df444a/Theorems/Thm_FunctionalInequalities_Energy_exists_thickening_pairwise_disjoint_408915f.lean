-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_exists_thickening_pairwise_disjoint_408915f
-- name    : FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:59.921477+00:00
-- url     : https://prove2.me/theorems/94a0b0f0-060a-4d3b-9b9b-4357606fe3a6
-- title:
--   Common Thickening Radius For Finitely Many Compact Sets
-- statement:
--   This is a metric separation lemma for finitely many pairwise disjoint compact sets.
--
--   Let $X$ be a metric space, let $N\in\mathbb N$, and let $K_i\subseteq X$ be compact for every $i\in\mathbb N$. Assume that distinct sets are pairwise disjoint:
--
--   $$
--    i\ne j\implies K_i\cap K_j=\varnothing.
--   $$
--
--   Then there exists a radius $\rho>0$ such that for all distinct $i,j<N$, the metric thickenings are disjoint:
--
--   $$
--   \operatorname{thickening}(\rho,K_i)\cap
--   \operatorname{thickening}(\rho,K_j)=\varnothing.
--   $$
--
--   The Lean declaration is `exists_thickening_pairwise_disjoint`. Only the first $N$ indices are required to have disjoint thickenings; the conclusion makes no assertion about indices at or beyond $N$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L121-L154 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint`; the repository is private at upload time).

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
section Separation
variable {X : Type*} [MetricSpace X]

theorem FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint_408915f (N : ℕ) (Kc : ℕ → Set X)
    (hcomp : ∀ n, IsCompact (Kc n)) (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i < N, ∀ j < N, i ≠ j →
      Disjoint (Metric.thickening ρ (Kc i)) (Metric.thickening ρ (Kc j)) := by sorry
