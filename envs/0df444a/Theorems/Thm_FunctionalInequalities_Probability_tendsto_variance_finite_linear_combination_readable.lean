-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_tendsto_variance_finite_linear_combination_readable
-- name    : FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:13.89698+00:00
-- url     : https://prove2.me/theorems/dd0e74f6-3d24-47af-bea4-9a629c78de4f
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_variance_finite_linear_combination
--       {alpha I : Type*} [MeasurableSpace alpha] [Fintype I]
--       (mu : ProbabilityMeasure alpha) (f : I → alpha → ℝ)
--       (hf : ∀ i, MemLp (f i) 2 (mu : Measure alpha))
--       (c : ℕ → I → ℝ) (b : I → ℝ)
--       (hc : ∀ i, Tendsto (fun k => c k i) atTop (𝓝 (b i))) :
--       Tendsto (fun k => ProbabilityTheory.variance (fun x => ∑ i, c k i * f i x) (mu : Measure alpha))
--         atTop (𝓝 (ProbabilityTheory.variance (fun x => ∑ i, b i * f i x) (mu : Measure alpha)))
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Previous: [`inner_center_center`](https://prove2.me/theorems/abb6082d-7b62-4620-a9a1-7ab8a33a4366).
--
--   [Source excerpt, lines 358–365](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/MeanVariance.lean#L358-L365) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/MeanVariance.lean#L358-L388 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.MeanVariance`, declaration `FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance

open MeasureTheory Filter
open scoped Topology

theorem FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination_readable
    {alpha I : Type*} [MeasurableSpace alpha] [Fintype I]
    (mu : ProbabilityMeasure alpha) (f : I → alpha → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (mu : Measure alpha))
    (c : ℕ → I → ℝ) (b : I → ℝ)
    (hc : ∀ i, Tendsto (fun k => c k i) atTop (𝓝 (b i))) :
    Tendsto (fun k => ProbabilityTheory.variance (fun x => ∑ i, c k i * f i x) (mu : Measure alpha))
      atTop (𝓝 (ProbabilityTheory.variance (fun x => ∑ i, b i * f i x) (mu : Measure alpha))) := by sorry
