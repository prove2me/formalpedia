-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_tendsto_integral_cond_closedBall_408915f
-- name    : FunctionalInequalities.KLS.tendsto_integral_cond_closedBall_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:22:25.268544+00:00
-- url     : https://prove2.me/theorems/4a46d646-7758-4a22-8c5f-3c44c313a2ce
-- title:
--   Convergence of Integrals After Conditioning on a Larger Ball
-- statement:
--   This statement formalizes the conditioning step of Letwin's Lemma A.1.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $(ν_k)$ and $μ$ be probability measures on $E$, with $ν_k\to μ$ in the topology of weak convergence. Let $r<R$, assume that $μ$ gives measure zero to the complement of $\overline B(0,r)$, and let $f:E\to\mathbb R$ be continuous. Then
--
--   $$
--   \int_E f(x)\,d\operatorname{cond}(ν_k,\overline B(0,R))(x)
--   \longrightarrow
--   \int_E f(x)\,dμ(x).
--   $$
--
--   The conclusion concerns the conditional probability measures `ProbabilityTheory.cond` on the closed ball; no boundedness assumption on $f$ is stated.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Conditioning.lean#L369-L480 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Conditioning`, declaration `FunctionalInequalities.KLS.tendsto_integral_cond_closedBall`; the repository is private at upload time).

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory
section LT10ABallConditioningMoments
open MeasureTheory Set Metric Filter
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS

theorem FunctionalInequalities.KLS.tendsto_integral_cond_closedBall_408915f {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hν : Tendsto ν atTop (𝓝 μ)) {r R : ℝ} (hrR : r < R)
    (hsupp : (μ : Measure E) (closedBall (0 : E) r)ᶜ = 0) {f : E → ℝ} (hf : Continuous f) :
    Tendsto (fun k => ∫ x, f x ∂(ProbabilityTheory.cond (ν k : Measure E) (closedBall (0 : E) R)))
      atTop (𝓝 (∫ x, f x ∂(μ : Measure E))) := by sorry
