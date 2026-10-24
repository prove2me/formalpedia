-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_patch_of_isCompact_408915f
-- name    : FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:09.366793+00:00
-- url     : https://prove2.me/theorems/83968bd2-bd10-4adf-bcfa-b0b07b6f486d
-- title:
--   Globally Lipschitz Patch From Finitely Many Compact Cores
-- statement:
--   This theorem constructs a global Lipschitz patch from finitely many disjoint compact cores.
--
--   Let $V$ be a normed additive group, let $f:V\to\mathbb R$ be globally $L$-Lipschitz, let $\alpha\ge0$, and let $N\in\mathbb N$. Let $K_n\subseteq V$ and $c_n\ge0$ satisfy
--
--   1. every $K_n$ is compact;
--   2. distinct $K_i,K_j$ are disjoint;
--   3. $f$ is $c_n$-Lipschitz on $K_n$;
--   4. $c_n\le L+\alpha$ for every $n$.
--
--   Then there exists $F:V\to\mathbb R$ such that
--
--   $$
--   \operatorname{LipschitzWith}(9L+8\alpha,F),
--   $$
--
--   and
--
--   $$
--   |F(x)-f(x)|\le 2L+2\alpha\quad\text{for every }x,
--   $$
--
--   while, for every $n<N$ and $x\in K_n$,
--
--   $$
--   F(x)=f(x),
--   \qquad
--   \operatorname{AsymptoticLipschitz.apply}(F,x)\le c_n.
--   $$
--
--   The declaration is `exists_patch_of_isCompact`. The constants $L$, $\alpha$, and $c_n$ are nonnegative-real parameters represented by `NNReal`; the pointwise asymptotic-Lipschitz bound is an `ENNReal` inequality.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L166-L548 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact`; the repository is private at upload time).

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
section Gluing
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact_408915f {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0}
    (N : ℕ) (Kc : ℕ → Set V) (c : ℕ → ℝ≥0) (hcomp : ∀ n, IsCompact (Kc n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j))
    (hlipK : ∀ n, LipschitzOnWith (c n) f (Kc n)) (hcle : ∀ n, c n ≤ L + α) :
    ∃ F : V → ℝ, LipschitzWith (9 * L + 8 * α) F ∧
      (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
      (∀ n < N, ∀ x ∈ Kc n, F x = f x) ∧
      (∀ n < N, ∀ x ∈ Kc n, AsymptoticLipschitz.apply F x ≤ (c n : ℝ≥0∞)) := by sorry
