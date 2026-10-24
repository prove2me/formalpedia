-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_tendsto_integral_scaled_mul_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:34.20576+00:00
-- url     : https://prove2.me/theorems/2e131de4-c6c5-4691-b545-5887ef38cb3d
-- title:
--   First and Second Integral Convergence Under Scaled Cutoffs
-- statement:
--   This statement gives convergence of the first and second integrals of cutoff products.
--
--   Let $E$ be a real inner product space with its Borel measurable structure, let $\mu$ be a finite measure on $E$, and let $f:E\to\mathbb R$ satisfy `MemLp f 2 μ`, including almost-everywhere strong measurability and finite $L^2$ seminorm. Write $\chi_R$ for `Energy.Euclidean.LipschitzApproximation.scaled R`.
--
--   Both limits hold as $n\in\mathbb N$ tends to infinity:
--   $$
--   \int\chi_{n+1}f\,d\mu\longrightarrow\int f\,d\mu,
--   \qquad
--   \int(\chi_{n+1}f)^2\,d\mu\longrightarrow\int f^2\,d\mu.
--   $$
--   These two scalar convergence statements support variance approximation by cutoff functions.
--
--   **Formalization Note** Neither completeness nor finite dimensionality of $E$ is assumed here. The conclusion is a conjunction of integral limits, not a statement of $L^2$-norm convergence.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L198-L324 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul`; the repository is private at upload time).

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
omit [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul_408915f {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => ∫ x, Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x ∂μ)
        atTop (𝓝 (∫ x, f x ∂μ)) ∧
      Tendsto (fun n : ℕ =>
          ∫ x, (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2 ∂μ)
        atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by sorry
