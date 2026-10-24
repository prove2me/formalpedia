-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_tendsto_energy_scaled_mul_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:32.27685+00:00
-- url     : https://prove2.me/theorems/15dff3e9-8663-45ab-bcd8-11b51449bfec
-- title:
--   Energy Convergence of Scaled Cutoff Products
-- statement:
--   This statement gives convergence of smooth-test energies under the designated expanding cutoffs.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure and $\mu$ a finite measure. Let $f:E\to\mathbb R$ be admissible (`Poincare.SmoothTest.Admissible`): $f$ is $C^\infty$, belongs to $L^2(\mu)$, and $\|\nabla f\|^2$ is integrable. For $R>0$, let $\chi_R$ denote `Energy.Euclidean.LipschitzApproximation.scaled R`. Define the energy (`Poincare.SmoothTest.energy`) by $\mathcal E_\mu(g)=\int\|\nabla g\|^2\,d\mu$.
--
--   As $n\in\mathbb N$ tends to infinity,
--   $$
--   \mathcal E_\mu(\chi_{n+1}f)\longrightarrow\mathcal E_\mu(f).
--   $$
--   This is an energy approximation statement for extending inequalities from compactly supported smooth tests to admissible tests. The energy has no factor of $1/2$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L421-L528 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul`; the repository is private at upload time).

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

theorem FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul_408915f {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : Admissible μ f) :
    Tendsto (fun n : ℕ =>
        energy μ (fun x => Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x))
      atTop (𝓝 (energy μ f)) := by sorry
