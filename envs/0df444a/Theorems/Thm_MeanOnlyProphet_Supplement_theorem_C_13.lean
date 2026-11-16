-- Prove2me | Theorems.Thm_MeanOnlyProphet_Supplement_theorem_C_13
-- name    : MeanOnlyProphet.Supplement.theorem_C_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:30:38.106686+00:00
-- url     : https://prove2.me/theorems/8a4ce10b-685e-490c-89dd-91f4935a5aca
-- title:
--   Theorem C.13 — continuous thresholds cannot guarantee $0.694451$ in prophet secretary
-- statement:
--   Let $U=0.694451$ and $\lambda=0.386571$. Consider deterministic thresholds $\theta:[0,1]\to[0,\infty)$ that are continuous and strictly decreasing with $\theta(1)=0$. Absolute continuity and $\theta(0)\le1$ are not assumed, and the threshold may depend on $n$. In prophet secretary the rule accepts the first value with $X_i>\theta(t_i)$ at its uniform arrival time $t_i$, and receives $0$ if no value is accepted.
--
--   1. For every $n\ge3$, every such $\theta$ and every $\zeta>0$, there are independent nonnegative values $X_1,\dots,X_n$ with finite means and $\mathbb E[X^*]=1$ on which
--   $$
--   \mathbb E[\mathrm{ALG}]\ \le\ U+\frac{\lambda}{n-1}+\zeta.
--   $$
--   2. No family $(\theta_n)_n$ of thresholds in this class guarantees a competitive ratio of $U$ for every $n$. That is, there is no family with $\mathbb E[\mathrm{ALG}_{\theta_n}]\ge U$ on every normalized independent nonnegative input with $n$ values, for every $n\ge1$.
--
--   The class of thresholds the paper's algorithms use therefore cannot certify a ratio above $0.6945$ in prophet secretary, which brackets Theorem 1.2's $0.6916$.
--
--   Differences from the source:
--   - encoding: θ : [0,1] → [0,∞) continuous, strictly decreasing, θ(1) = 0 → θ : ℝ → ℝ with ContinuousOn, StrictAntiOn and nonnegativity on [0,1] and θ 1 = 0; reason: arrival times lie in [0,1], so values outside it are never used
--   - encoding: nonnegative independent input with E[X*] = 1 → probability laws μ i with μ i((−∞,0)) = 0, Integrable id (μ i) and psProphetMean μ = 1; reason: integrability follows from E[X*] = 1 for nonnegative values
--   - encoding: threshold θ(t_i) → psExpectedReward, whose threshold is E[X*] · θ(t_i) = θ(t_i) on these inputs; reason: same rule
--   - encoding: no family guarantees a competitive ratio of U for every n → ¬ ∃ θs : ℕ → (ℝ → ℝ) in the class with U ≤ E[ALG] on every normalized input for every n ≥ 1; reason: §2's definition of γ-competitive on normalized inputs
--   - encoding: λ/(n − 1) → 0.386571 / ((n : ℝ) − 1); reason: real division, n ≥ 3
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Theorem C.13, p.53 (PDF p.54); class App. C.2, p.48 (PDF p.49)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Supplement_psExpectedReward

open MeasureTheory

namespace MeanOnlyProphet.Supplement

/-- **Theorem C.13 (upper bound for non-adaptive continuous thresholds in prophet secretary).** Feng,
Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…),
Theorem C.13, p.53 (PDF p.54): "Let U = 0.694451 and λ = 0.386571. For every n ≥ 3, every threshold in
the above class, and every ζ > 0, there is a nonnegative independent input with E[X ∗ ] = 1 such that
E[ALG] ≤ U + λ/(n − 1) + ζ. Moreover, no family of thresholds in this class guarantees a competitive
ratio of U for every n." The class is that of App. C.2, p.48 (PDF p.49): "deterministic, continuous,
strictly decreasing threshold functions θ : [0, 1] → [0, ∞) satisfying θ(1) = 0, without assuming
absolute continuity or imposing θ(0) ≤ 1. The threshold may depend on n … The algorithm accepts the
first value Xi satisfying Xi > θ(ti ) at its arrival time ti , and receives zero if no value is
accepted."

(i) For every `n ≥ 3`, every such `θ` and every `ζ > 0` there are independent nonnegative laws
`μ_1, …, μ_n` with finite means and `E[X*] = 1` on which the rule earns
`E[ALG] ≤ 0.694451 + 0.386571/(n − 1) + ζ`. (ii) There is no family `(θ_n)` in the class with
`E[ALG_{θ_n}] ≥ 0.694451` on every such normalized input, for every `n ≥ 1`.

**Formalization Note.** The class is `ContinuousOn`, `StrictAntiOn` and nonnegative on `[0,1]` with
`θ 1 = 0`. On inputs with `E[X*] = 1` the published-model rule `psExpectedReward` uses the threshold
`1 · θ(t_i) = θ(t_i)`. `(n : ℝ) − 1` is real subtraction. In (ii) the family `θs : ℕ → ℝ → ℝ` may
depend on `n`; "competitive ratio U" on normalized inputs is `U ≤ E[ALG]`. -/
theorem theorem_C_13 :
    (∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ θ : ℝ → ℝ,
      ContinuousOn θ (Set.Icc 0 1) → StrictAntiOn θ (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ θ t) → θ 1 = 0 →
      ∀ ζ : ℝ, 0 < ζ →
        ∃ μ : Fin n → Measure ℝ, (∀ i, IsProbabilityMeasure (μ i)) ∧
          (∀ i, μ i (Set.Iio 0) = 0) ∧ (∀ i, Integrable id (μ i)) ∧ psProphetMean μ = 1 ∧
          psExpectedReward θ μ ≤ 0.694451 + 0.386571 / ((n : ℝ) - 1) + ζ) ∧
    ¬ ∃ θs : ℕ → ℝ → ℝ,
      (∀ n, ContinuousOn (θs n) (Set.Icc 0 1) ∧ StrictAntiOn (θs n) (Set.Icc 0 1) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ θs n t) ∧ θs n 1 = 0) ∧
      ∀ (n : ℕ) [NeZero n] (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)],
        (∀ i, μ i (Set.Iio 0) = 0) → (∀ i, Integrable id (μ i)) → psProphetMean μ = 1 →
          (0.694451 : ℝ) ≤ psExpectedReward (θs n) μ := by sorry

end MeanOnlyProphet.Supplement
