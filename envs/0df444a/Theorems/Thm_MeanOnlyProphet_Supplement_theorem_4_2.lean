-- Prove2me | Theorems.Thm_MeanOnlyProphet_Supplement_theorem_4_2
-- name    : MeanOnlyProphet.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:29:20.446995+00:00
-- url     : https://prove2.me/theorems/646fb722-9f9c-419e-bd80-fe64679e75fd
-- title:
--   Theorem 4.2 — the two-step threshold earns $0.6385\,\mathbb E[X^*]$ in prophet secretary
-- statement:
--   Let $\theta(t)=2/3-t/2$ for $0\le t\le2/3$ and $\theta(t)=1-t$ for $2/3\le t\le1$. This is the threshold of the two-step drop rate $b=1/2$ on $[0,2/3)$ and $b=1$ on $[2/3,1]$. Let $n\ge1$, and let $X_1,\dots,X_n$ be independent nonnegative values with finite means and arbitrary laws. Let them arrive at independent uniform times $t_i\in[0,1]$. The rule that accepts the first arrival with $X_i>\mathbb E[X^*]\cdot\theta(t_i)$ earns
--   $$
--   \mathbb E[\mathrm{ALG}]\ \ge\ 0.6385\cdot\mathbb E[X^*].
--   $$
--   A threshold with only two linear pieces already beats the classical prophet-secretary ratio $1-1/e\approx0.632$.
--
--   Differences from the source:
--   - encoding: competitive ratio of at least 0.6385 under the normalization E[X*] = 1 (§2) → 0.6385 · E[X*] ≤ E[ALG] on all inputs, with the threshold scaled by E[X*]; reason: the rule is scale invariant, and inputs with E[X*] = 0 are almost surely zero, so the two forms are the same claim
--   - encoding: independent nonnegative random variables in uniformly random order → probability laws μ i with μ i((−∞,0)) = 0, Measure.pi, and i.i.d. uniform arrival times on [0,1]; reason: §2 represents the random order by these arrival times
--   - encoding: finite E[X*] → Integrable id (μ i) for every i; reason: for nonnegative values E[X*] < ∞ exactly when every mean is finite
--   - encoding: ties between arrival times → broken by the least index; reason: they have probability zero
--   - encoding: for every n → every n with NeZero n (n ≥ 1); reason: n counts the values
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §4.2, Theorem 4.2, p.13 (PDF p.14); model §2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Supplement_psExpectedReward
import Definitions.Def_MeanOnlyProphet_Supplement_twoStepTheta

open MeasureTheory

namespace MeanOnlyProphet.Supplement

/-- **Theorem 4.2 (two-step drop rate, prophet secretary, 0.6385).** Feng, Jin, Wu, Xiang, *Mean-only
Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), §4.2, p.13 (PDF p.14): "Choose
b(t) = 1/2, 0 ≤ t < 2/3; 1, 2/3 ≤ t ≤ 1, θ(t) = ∫_t^1 b(s) ds = 2/3 − t/2, 0 ≤ t ≤ 2/3; 1 − t,
2/3 ≤ t ≤ 1. Theorem 4.2. For the prophet secretary, the two-step drop rate above guarantees a
competitive ratio of at least 0.6385 for every n."

For every `n ≥ 1` and all independent nonnegative values with finite means and arbitrary laws, the
prophet-secretary rule with threshold `E[X*] · θ(t_i)`, `θ = twoStepTheta`, earns
`E[ALG] ≥ 0.6385 · E[X*]`.

**Formalization Note.** The paper's "competitive ratio" is stated under the normalization
`E[X*] = 1` (§2); the rule scales `θ` by `E[X*]`, so the unnormalized form here is the same claim.
Strict acceptance; reward `0` if no value passes. `0.6385` is an exact decimal. -/
theorem theorem_4_2 :
    ∀ (n : ℕ) [NeZero n] (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)],
      (∀ i, μ i (Set.Iio 0) = 0) → (∀ i, Integrable id (μ i)) →
        (0.6385 : ℝ) * psProphetMean μ ≤ psExpectedReward twoStepTheta μ := by sorry

end MeanOnlyProphet.Supplement
