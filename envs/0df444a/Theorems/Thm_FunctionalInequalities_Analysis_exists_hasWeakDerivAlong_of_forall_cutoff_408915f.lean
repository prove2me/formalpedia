-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_hasWeakDerivAlong_of_forall_cutoff_408915f
-- name    : FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_forall_cutoff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:44.615742+00:00
-- url     : https://prove2.me/theorems/9c82da3d-62ab-4334-9a97-9cf288433228
-- title:
--   Gluing Local Weak Derivatives From Compact Cutoffs
-- statement:
--   This is a generic gluing theorem for weak derivatives.
--
--   Let $E$ be a finite-dimensional real inner-product normed space with its Borel measurable structure, and let $f:E\to\mathbb R$. Assume:
--
--   1. for every compact set $S$, the restriction of $f$ to $S$ belongs to $L^2$ with respect to restricted volume;
--   2. for every $C^1$ compactly supported cutoff $\chi$, there is a globally $L^2$ function $g_\chi$ such that $\chi f$ has weak derivative $g_\chi$ along a fixed vector $v$.
--
--   Then there exists $g:E\to\mathbb R$ such that $g$ is a weak derivative of $f$ along $v$, and for every compact $S$, $g$ belongs to $L^2$ with respect to volume restricted to $S$.
--
--   The conclusion is local $L^2$ regularity of the derivative rather than global $L^2$ regularity. It provides a cutoff-gluing interface for weak derivative constructions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L24-L139 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Approximation`, declaration `FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_forall_cutoff`; the repository is private at upload time).

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
section LN11C2WeakDerivativeGluing
open MeasureTheory Set Filter Metric
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_forall_cutoff_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ∀ S : Set E, IsCompact S → MemLp f 2 ((volume : Measure E).restrict S)) (v : E)
    (hloc : ∀ χ : E → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
      ∃ g : E → ℝ, HasWeakDerivAlong (fun x => χ x * f x) g v ∧ MemLp g 2 (volume : Measure E)) :
    ∃ g : E → ℝ, HasWeakDerivAlong f g v ∧
      ∀ S : Set E, IsCompact S → MemLp g 2 ((volume : Measure E).restrict S) := by sorry
