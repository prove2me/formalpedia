-- Prove2me | Theorems.Thm_MPBSelect_Supplement_theorem_1
-- name    : MPBSelect.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:47:50.068083+00:00
-- url     : https://prove2.me/theorems/2b4cd6b5-98bb-4d87-81f7-567d480f661d
-- title:
--   Theorem 1 — exact inner, outer and total false-selection rates
-- statement:
--   Consider the finite MPB model, a feasible fixed allocation $\boldsymbol\alpha$, and a deterministic allocation rule with total count $n$, $N_i^n(\theta_b)/n\to\alpha_i(\theta_b)$ and $N_i^n(\theta_b)\to\infty$ for every pair. Simulation outputs are mutually independent Gaussians with mean $y_i(\theta_b)$ and variance $\lambda_i^2(\theta_b)$, and the estimated conditional optima are $i^b_n=\arg\min_i\mu_{i,n}(\theta_b)$ for the posterior means (5) under any normal prior (zero prior precision gives the sample means).
--
--   **Theorem 1.** With $\widetilde G_i(\theta_b)$ defined by (14) and $\widetilde{\mathrm{LDR}}_{j,i^*}$ the minimum, over mappings in $\mathcal A_j$, of the sum of the exact inner rates on their misspecified pairs:
--
--   1. for every pair $(i,\theta_b)$ (for $i=i^b$ both sides are $0$), the lower exponential rate of selecting $i$ as the conditional optimum at $\theta_b$ equals $\widetilde G_i(\theta_b)$;
--   2. for every $j\ne i^*$, the lower exponential rate of the estimated mapping lying in $\mathcal A_j$ equals $\widetilde{\mathrm{LDR}}_{j,i^*}$;
--   3. the lower exponential rate of the set-valued false-selection event equals $\min_{j\ne i^*}\widetilde{\mathrm{LDR}}_{j,i^*}$.
--
--   This identifies the exact nested large-deviations objective before either relaxation used later in the paper.
--
--   Differences from the source:
--   - encoding: one-hot conditional-optimum matrices and ordinary negative logarithms → mappings `Fin B → Fin k` and extended-real negative logarithms; reason: the representations are equivalent, while the extended value gives a probability-zero event rate $+\infty$ instead of Lean's `Real.log 0=0`
--   - encoding: fixed allocation rule with $N_i^n/n\to\alpha_i$ and $N_i^n\to\infty$ stated in the section preamble → these conditions, feasibility and total count are explicit theorem hypotheses; reason: they are the standing assumptions on p.11
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 1, (14), p.13; static-allocation assumptions p.11

import Mathlib
import Definitions.Def_MPBSelect_feasibleSet
import Definitions.Def_MPBSelect_Supplement_ExactRates

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace MPBSelect.Supplement

/-- **Theorem 1 (exact false-selection large-deviations rates).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 1,
p.13, equation (14).

For every feasible fixed allocation and deterministic rule whose counts have those limiting
ratios, under independent Gaussian outputs: (i) the inner false-selection event has rate
`G̃_i(θ_b)`; (ii) each outer comparison event has the minimum summed mapping rate; and (iii)
the set-valued false-selection event has the minimum outer comparison rate.

**Formalization Note** The estimated mapping uses the posterior means (5) under an arbitrary
normal prior `pr` (zero precision is the noninformative prior, where they are sample means), as
in (7). Part (i) is stated for every pair `(i,θ_b)`, as printed; at `i = i^b` both sides are `0`.
`EReal` records the correct `+∞` value if an event has probability zero.
Mappings are functions `Fin B → Fin k`, equivalent to the paper's one-hot matrices. -/
theorem theorem_1 {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) (hα : α ∈ MPBSelect.feasibleSet k B)
    (N : ℕ → Fin k → Fin B → ℕ)
    (hNtotal : ∀ n, ∑ i, ∑ b, N n i b = n)
    (hNratio : ∀ i b, Tendsto (fun n : ℕ => (N n i b : ℝ) / (n : ℝ)) atTop (𝓝 (α i b)))
    (hNinf : ∀ i b, Tendsto (fun n => N n i b) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (hY : IsGaussianSamples P μ Y)
    (pr : GaussianPrior k B) :
    (∀ i b,
      eventLiminfRate μ (fun n => innerSelectionEvent P pr N Y i b n) =
        (exactInnerRate P α i b : EReal)) ∧
    (∀ j, j ≠ P.istar →
      eventLiminfRate μ (fun n => outerComparisonEvent P pr N Y j n) =
        (exactOuterRate P α j : EReal)) ∧
    eventLiminfRate μ (fun n => falseSelectionEvent P pr N Y n) =
      (exactFSRate P α : EReal) := by sorry

end MPBSelect.Supplement
