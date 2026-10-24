-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_patch_408915f
-- name    : FunctionalInequalities.Energy.LocalSlope.exists_patch_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:10.388628+00:00
-- url     : https://prove2.me/theorems/e7ab1540-3203-4d0b-adb7-63bf6c0dbeae
-- title:
--   Large-Measurable-Set Lipschitz Patch
-- statement:
--   This theorem produces a globally Lipschitz approximation agreeing with a globally Lipschitz function on most of a probability space.
--
--   Let $V$ be a finite-dimensional real inner-product normed space with its Borel measurable structure, let $\nu$ be a probability measure on $V$, and let $f:V\to\mathbb R$ be globally $L$-Lipschitz. Let $\alpha>0$ be represented by `NNReal`, and let $\delta>0$ be an `ENNReal` value. Then there exist a function $F:V\to\mathbb R$ and a measurable set $K\subseteq V$ such that
--
--   1. $F$ is globally $(9L+8\alpha)$-Lipschitz;
--   2. $\nu(K^c)\le\delta$;
--   3. $F=f$ on $K$;
--   4. for every $x\in V$,
--      $$
--      |F(x)-f(x)|\le 2L+2\alpha;
--      $$
--   5. for every $x\in K$,
--      $$
--      \operatorname{AsymptoticLipschitz.apply}(F,x)
--      \le \operatorname{apply}(f,x)+2\alpha.
--      $$
--
--   The declaration is `exists_patch`. The measure bound and slope comparison use $[0,\infty]$ values (`ENNReal`), and the conclusion is existential for each strictly positive $\alpha$ and $\delta$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L681-L753 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.LocalSlope.exists_patch`; the repository is private at upload time).

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
omit [CompleteSpace V]

theorem FunctionalInequalities.Energy.LocalSlope.exists_patch_408915f (ν : ProbabilityMeasure V) {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {α : ℝ≥0} (hα : 0 < α) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ (F : V → ℝ) (K : Set V), LipschitzWith (9 * L + 8 * α) F ∧ MeasurableSet K ∧
      (ν : Measure V) Kᶜ ≤ δ ∧ (∀ x ∈ K, F x = f x) ∧
      (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
      ∀ x ∈ K, AsymptoticLipschitz.apply F x ≤ apply f x + 2 * (α : ℝ≥0∞) := by sorry
