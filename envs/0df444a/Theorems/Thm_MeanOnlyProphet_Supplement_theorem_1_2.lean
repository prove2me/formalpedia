-- Prove2me | Theorems.Thm_MeanOnlyProphet_Supplement_theorem_1_2
-- name    : MeanOnlyProphet.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:28:13.672474+00:00
-- url     : https://prove2.me/theorems/b960f1eb-3888-4c1e-88a8-3373b83496bc
-- title:
--   Theorem 1.2 — a mean-only threshold earns $0.6916\,\mathbb E[X^*]$ in prophet secretary
-- statement:
--   There is a single threshold function $\theta$ with the following property. It is continuous, concave and strictly decreasing on $[0,1]$, with $\theta(1)=0$ and $\theta(0)\le1$. Let $n\ge1$, and let $X_1,\dots,X_n$ be independent nonnegative values with finite means and arbitrary laws $\mu_1,\dots,\mu_n$. Let them arrive at independent uniform times $t_i\in[0,1]$, and write $X^*=\max_iX_i$. The rule that accepts the first arrival with $X_i>\mathbb E[X^*]\cdot\theta(t_i)$ then earns
--   $$
--   \mathbb E[\mathrm{ALG}]\ \ge\ 0.6916\cdot\mathbb E[X^*].
--   $$
--   The rule knows only $n$ and $\mathbb E[X^*]$, and $\theta$ is fixed before $n$ and the laws. The guarantee exceeds the best known full-information ratio $0.688$ for prophet secretary.
--
--   Differences from the source:
--   - generalization: a non-adaptive algorithm with a continuous concave decreasing threshold function → the threshold rule with a θ that is continuous, concave and strictly decreasing on [0,1], with θ(1) = 0 and θ(0) ≤ 1; reason: a narrower witness makes the ∃ stronger; the extra properties are §2's standing restriction (thresholds strictly decrease to zero) and θ(0) = ∫b ≤ 1
--   - encoding: competitive ratio under the normalization E[X*] = 1 (§2) → all inputs, with the threshold scaled by E[X*]; reason: the theorem's display is E[ALG] ≥ 0.6916 · E[X*]; the rule is scale invariant, so the two forms are the same claim
--   - encoding: independent nonnegative random variables in uniformly random order → probability laws μ i with μ i((−∞,0)) = 0, Measure.pi, and i.i.d. uniform arrival times on [0,1]; reason: §2 represents the random order by these arrival times
--   - encoding: the algorithm knows E[X*] (finite) → Integrable id (μ i) for every i; reason: for nonnegative values E[X*] < ∞ exactly when every mean is finite
--   - encoding: ties between arrival times → broken by the least index; reason: they have probability zero
--   - encoding: for every n → every n with NeZero n (n ≥ 1); reason: n counts the values
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Theorem 1.2, p.2 (PDF p.3); model §2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Supplement_psExpectedReward

open MeasureTheory

namespace MeanOnlyProphet.Supplement

/-- **Theorem 1.2 (prophet secretary, mean-only, 0.6916).** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), Theorem 1.2, p.2 (PDF p.3): "There
is a non-adaptive algorithm with a continuous concave decreasing threshold function for prophet
secretary such that, for every n, E[ALG] ≥ 0.6916 · E[X∗]."

There is one threshold `θ`, continuous, concave and strictly decreasing on `[0,1]` with `θ(1) = 0` and
`θ(0) ≤ 1`, such that for every `n ≥ 1` and all independent nonnegative values with finite means and
arbitrary laws `μ_1, …, μ_n`, arriving at independent uniform times `t_i ∈ [0,1]`, the rule "accept
the first arrival with `X_i > E[X*] · θ(t_i)`" earns `E[ALG] ≥ 0.6916 · E[X*]`.

**Formalization Note.** `θ` is chosen before `n` and the laws. Sample space `(Fin n → ℝ) × (Fin n → ℝ)`
(values, arrival times); strict acceptance; reward `0` if no value passes (no forced acceptance).
Nonnegativity is `μ_i((−∞,0)) = 0`, finite mean `Integrable id (μ i)`. `0.6916` is an exact decimal. -/
theorem theorem_1_2 :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Set.Icc 0 1) ∧ ConcaveOn ℝ (Set.Icc 0 1) θ ∧
      StrictAntiOn θ (Set.Icc 0 1) ∧ θ 1 = 0 ∧ θ 0 ≤ 1 ∧
      ∀ (n : ℕ) [NeZero n] (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)],
        (∀ i, μ i (Set.Iio 0) = 0) → (∀ i, Integrable id (μ i)) →
          (0.6916 : ℝ) * psProphetMean μ ≤ psExpectedReward θ μ := by sorry

end MeanOnlyProphet.Supplement
