-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_Admissible_of_contDiff_hasCompactSupport_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:31.345843+00:00
-- url     : https://prove2.me/theorems/46a5a432-d5d9-4680-a2d6-72742656114b
-- title:
--   Compactly Supported Smooth Functions Are Admissible
-- statement:
--   This auxiliary statement supplies admissible smooth Poincaré tests for every finite measure.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure, let $\mu$ be a finite measure on $E$, and let $f:E\to\mathbb R$ be $C^\infty$ with compact support.
--
--   Then $f$ is admissible (`Poincare.SmoothTest.Admissible`):
--   $$
--   f\in C^\infty(E),\qquad f\in L^2(\mu),\qquad
--   \bigl(x\mapsto\|\nabla f(x)\|^2\bigr)\in L^1(\mu).
--   $$
--   This provides tests usable in the smooth-test Poincaré inequality without a probability or density assumption on the measure.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L158-L186 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
section Cutoff
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport_408915f {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Admissible μ f := by sorry
