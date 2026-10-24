-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_variance_le_mul_energy_of_tendsto_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.variance_le_mul_energy_of_tendsto_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:31.706721+00:00
-- url     : https://prove2.me/theorems/a799273c-fd40-4062-85eb-e40a8d7e96ad
-- title:
--   Weak-Limit Passage for a Fixed Compactly Supported Smooth Test
-- statement:
--   This is a fixed-test weak-limit transfer statement associated with Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered), and its regular-approximation reduction.
--
--   Let $E$ be a complete real inner product space with its Borel measurable structure. Assume:
--
--   1. Probability measures $\mu_j$ converge weakly to a probability measure $\mu$ as $j\in\mathbb N$ tends to infinity.
--   2. Real numbers $C_j$ converge to $C\in\mathbb R$.
--   3. $f:E\to\mathbb R$ is $C^\infty$ with compact support.
--   4. For every $j$, $\operatorname{Var}_{\mu_j}(f)\le C_j\int\|\nabla f\|^2\,d\mu_j$.
--
--   Then
--   $$
--   \operatorname{Var}_\mu(f)\le C\int\|\nabla f\|^2\,d\mu.
--   $$
--   This transfers the inequality for the specified test, rather than asserting a bound for all tests at once.
--
--   **Formalization Note** The energy is `Poincare.SmoothTest.energy`, and variance is `ProbabilityTheory.variance`. No finite-dimensionality, log-concavity, or nonnegativity assumption on $C_j$ or $C$ is present.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L29-L152 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.variance_le_mul_energy_of_tendsto`; the repository is private at upload time).

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

theorem FunctionalInequalities.Poincare.SmoothTest.variance_le_mul_energy_of_tendsto_408915f {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hlim : Tendsto μs atTop (𝓝 μ)) {Cseq : ℕ → ℝ} {C : ℝ} (hC : Tendsto Cseq atTop (𝓝 C))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (h : ∀ j, variance f (μs j : Measure E) ≤ Cseq j * energy (μs j : Measure E) f) :
    variance f (μ : Measure E) ≤ C * energy (μ : Measure E) f := by sorry
