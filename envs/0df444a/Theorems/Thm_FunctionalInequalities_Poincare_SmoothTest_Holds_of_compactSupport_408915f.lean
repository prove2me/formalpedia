-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_Holds_of_compactSupport_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:31.800074+00:00
-- url     : https://prove2.me/theorems/38c3861a-80ca-4689-9d8a-cdf28d3cc316
-- title:
--   Extension of Compactly Supported Smooth-Test Poincaré Bounds
-- statement:
--   This is the compact-support extension step associated with the regular-approximation reduction in Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered).
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure, let $\mu$ be a probability measure, and let $C\in\mathbb R$. Assume:
--
--   1. $C\ge0$.
--   2. Every compactly supported admissible $f:E\to\mathbb R$ satisfies $\operatorname{Var}_\mu(f)\le C\mathcal E_\mu(f)$.
--
--   Here admissibility (`Poincare.SmoothTest.Admissible`) means $C^\infty$ smoothness, membership in $L^2(\mu)$, and integrability of $\|\nabla f\|^2$; $\mathcal E_\mu(f)=\int\|\nabla f\|^2\,d\mu$ is `Poincare.SmoothTest.energy`.
--
--   Then `Poincare.SmoothTest.Holds μ C` holds, namely
--   $$
--   \operatorname{Var}_\mu(f)\le C\int\|\nabla f\|^2\,d\mu
--   \quad\text{for every admissible }f.
--   $$
--   This removes the compact-support restriction on the tests. It does not assume log-concavity or establish the paper's regular-density conditions.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L530-L594 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport`; the repository is private at upload time).

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

theorem FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport_408915f {μ : Measure E} [IsProbabilityMeasure μ] {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : E → ℝ, Admissible μ f → HasCompactSupport f → variance f μ ≤ C * energy μ f) :
    Holds μ C := by sorry
