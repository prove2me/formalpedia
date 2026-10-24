-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_partition_408915f
-- name    : FunctionalInequalities.Energy.LocalSlope.exists_partition_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:04.484461+00:00
-- url     : https://prove2.me/theorems/a3b49b2c-13d0-45d6-827b-7536389c7aef
-- title:
--   Measurable Partition By Local-Slope Bands
-- statement:
--   This theorem constructs a measurable partition adapted to the local slope of a globally Lipschitz function.
--
--   Let $V$ be a second-countable Borel measurable normed additive group, let $f:V\to\mathbb R$ be globally $L$-Lipschitz with $L\in[0,\infty)$, and let $\alpha>0$ be represented by `NNReal`. Then there exist sets $D_i\subseteq V$ and constants $c_i\in[0,\infty)$, indexed by $i\in\mathbb N$, such that
--
--   1. every $D_i$ is measurable;
--   2. the sets $D_i$ are pairwise disjoint and cover $V$;
--   3. $c_i\le L+\alpha$ for every $i$;
--   4. $f$ is $c_i$-Lipschitz on $D_i$;
--   5. for every $x\in D_i$,
--      $$
--      c_i\le \operatorname{apply}(f,x)+\alpha.
--      $$
--
--   The Lean declaration is `exists_partition`. The local slope and the final comparison are expressed in `ENNReal`, while $L$, $\alpha$, and $c_i$ are nonnegative real constants represented by `NNReal`. This is a technical partition lemma used in patching arguments.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L563-L679 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.LocalSlope.exists_partition`; the repository is private at upload time).

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
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Patch
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.LocalSlope.exists_partition_408915f {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0} (hα : 0 < α) :
    ∃ (D : ℕ → Set V) (c : ℕ → ℝ≥0),
      (∀ i, MeasurableSet (D i)) ∧ Pairwise (Function.onFun Disjoint D) ∧
      (⋃ i, D i) = Set.univ ∧ (∀ i, c i ≤ L + α) ∧
      (∀ i, LipschitzOnWith (c i) f (D i)) ∧
      (∀ i, ∀ x ∈ D i, ((c i : ℝ≥0∞)) ≤ apply f x + (α : ℝ≥0∞)) := by sorry
