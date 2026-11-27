-- Prove2me | Theorems.Thm_MPBSelect_Supplement_theorem_EC_1
-- name    : MPBSelect.Supplement.theorem_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:52:32.488371+00:00
-- url     : https://prove2.me/theorems/e58a7e18-c92d-5d4e-bca5-26e047b71d29
-- title:
--   Theorem EC.1 — false-selection LDR bound for non-unique MPBs
-- statement:
--   Let $i^*$ be the nonempty set of all solutions with maximal preference probability, retaining the finite-support model, pairwise-distinct conditional means, independent Gaussian outputs, posterior means (5) under any normal prior, and a feasible fixed allocation whose every count diverges. Then the set-valued false-selection event satisfies
--
--   $$
--   \liminf_{n\to\infty}-\frac1n\log P(i_n^*\ne i^*)
--   \ge \min_{(i,\theta_b)\in\bigcup_{\ell\in i^*}\Xi_\ell}
--     \left(\min_{\ell\in i^*}W_i^\ell(\theta_b)\right)G_i(\theta_b).
--   $$
--
--   The inner and outer minima and the set-valued error event are retained exactly.
--
--   Differences from the source:
--   - encoding: $i^*=\arg\max_jP_j$ and $i_n^*$ are sets written with overloaded symbols → explicit nonempty finite sets of all maximizers; reason: equality and false selection remain set-valued exactly as printed
--   - encoding: ordinary negative logarithm and $+\infty$ weights → extended-real logarithm and weights; reason: zero-probability events and pairs outside $\Xi_\ell$ receive their mathematical extended values rather than Lean defaults
--   - encoding: the fixed-allocation assumptions are inherited from §4.1 → feasibility, total counts, limiting ratios and diverging counts are explicit; reason: Theorem EC.1 extends Theorem 2 under the same static Gaussian allocation model
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem EC.1 and (EC.29), p.ec14 (PDF p.57); continuation p.ec15

import Mathlib
import Definitions.Def_MPBSelect_Supplement_Nonunique

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace MPBSelect.Supplement

/-- **Theorem EC.1 (extension to non-unique MPBs).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2,
Theorem EC.1, p.ec14 (PDF p.57), equation (EC.29).

For the set-valued MPB estimator, the false-selection LDR is at least the minimum over
`⋃_{ell∈i*} Ξ_ell` of `(min_{ell∈i*} W_i^ell(θ_b)) G_i(θ_b)`. -/
theorem theorem_EC_1 {k B : ℕ} (P : NonuniqueProblem k B)
    (α : Fin k → Fin B → ℝ)
    (hαsum : ∑ i, ∑ b, α i b = 1) (hαnonneg : ∀ i b, 0 ≤ α i b)
    (N : ℕ → Fin k → Fin B → ℕ)
    (hNtotal : ∀ n, ∑ i, ∑ b, N n i b = n)
    (hNratio : ∀ i b, Tendsto (fun n : ℕ => (N n i b : ℝ) / (n : ℝ)) atTop (𝓝 (α i b)))
    (hNinf : ∀ i b, Tendsto (fun n => N n i b) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (hY : P.IsGaussianSamples μ Y)
    (pr : GaussianPrior k B) :
    P.ldrLowerBound α ≤ eventLiminfRate μ (fun n => P.falseSelectionEvent pr N Y n) := by sorry

end MPBSelect.Supplement
