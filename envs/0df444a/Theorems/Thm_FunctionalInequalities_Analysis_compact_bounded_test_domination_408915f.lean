-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_compact_bounded_test_domination_408915f
-- name    : FunctionalInequalities.Analysis.compact_bounded_test_domination_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:36.345859+00:00
-- url     : https://prove2.me/theorems/13f223a6-3775-4b2b-aafb-c82cde94f380
-- title:
--   Compact Support Domination for Bounded Tests
-- statement:
--   This gives an integrable domination statement for a compactly supported bounded test.
--
--   Let $F,\eta:\mathbb R^n\to\mathbb R$, let $S\subseteq\mathbb R^n$ be compact, and let $C\in\mathbb R$. Assume $F$ is locally integrable, $\eta$ is almost-everywhere strongly measurable, $\operatorname{supp}(\eta)\subseteq S$, and $\|\eta(x)\|\le C$ for every $x$. Then
--
--   $$
--   \mathbf 1_S(x)C\|F(x)\|
--   $$
--
--   is integrable, and for every $x$,
--
--   $$
--   \|F(x)\eta(x)\|\le \mathbf 1_S(x)C\|F(x)\|.
--   $$
--
--   Consequently $x\mapsto F(x)\eta(x)$ is integrable with respect to volume measure. The Lean declaration is `compact_bounded_test_domination`; the hypotheses are pointwise except for the stated a.e. measurability condition.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1088-L1117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.compact_bounded_test_domination`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section BoundedWeakDerivativeTesting
open MeasureTheory Filter Set
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.compact_bounded_test_domination_408915f {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {C : ℝ} (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hsupp : Function.support η ⊆ S) (hbound : ∀ x, ‖η x‖ ≤ C) :
    Integrable (S.indicator fun x => C * ‖F x‖)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ x, ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x) ∧
      Integrable (fun x => F x * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
