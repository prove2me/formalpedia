-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_tendsto_variance_finite_linear_combination_408915f
-- name    : FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:26:26.548475+00:00
-- url     : https://prove2.me/theorems/90471a0f-93b5-4deb-a263-cb8de9a750cb
-- title:
--   Continuity of Variance for Finite Linear Combinations
-- statement:
--   This is a finite-dimensional coefficient-continuity lemma for variance.
--
--   Let $\mu$ be a probability measure on a measurable space $\alpha$, let $I$ be a finite index type, and let $f_i:\alpha\to\mathbb R$ satisfy $f_i\in L^2(\mu)$ for every $i$. If $c_k(i)\to b(i)$ for every $i\in I$, then
--
--   $$\operatorname{Var}_{\mu}\!\left(x\mapsto\sum_i c_k(i)f_i(x)\right)
--   \longrightarrow
--   \operatorname{Var}_{\mu}\!\left(x\mapsto\sum_i b(i)f_i(x)\right).$$
--
--   The conclusion is an ordinary real-valued limit of variances and is useful for passing coefficient approximations through quadratic or matrix observables.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/MeanVariance.lean#L358-L388 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.MeanVariance`, declaration `FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
noncomputable section
open MeasureTheory Filter
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability

theorem FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination_408915f
    {alpha I : Type*} [MeasurableSpace alpha] [Fintype I]
    (mu : ProbabilityMeasure alpha) (f : I → alpha → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (mu : Measure alpha))
    (c : ℕ → I → ℝ) (b : I → ℝ)
    (hc : ∀ i, Tendsto (fun k => c k i) atTop (𝓝 (b i))) :
    Tendsto (fun k => ProbabilityTheory.variance (fun x => ∑ i, c k i * f i x) (mu : Measure alpha))
      atTop (𝓝 (ProbabilityTheory.variance (fun x => ∑ i, b i * f i x) (mu : Measure alpha))) := by sorry
