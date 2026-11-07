-- Prove2me | Theorems.Thm_MeanOnlyProphet_theorem_1_1
-- name    : MeanOnlyProphet.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:27:07.010844+00:00
-- url     : https://prove2.me/theorems/5f37df70-a0d4-4635-b8ce-d1783f887439
-- title:
--   Theorem 1.1 — a mean-only concave threshold earns $0.7419\,\mathbb E[X^*]$ for i.i.d. values and every $n$
-- statement:
--   There is a single threshold function $\theta$, continuous, concave and strictly decreasing on $[0,1]$ with $\theta(1)=0$ and $\theta(0)\le1$, with the following property. For every $n\ge1$ and every law $\mu$ of nonnegative values with finite mean, let $X_1,\dots,X_n$ be i.i.d. with law $\mu$, $X^*=\max_iX_i$, and run the randomly shifted rule: draw $U$ uniform on $[0,1]$ independently of the values, accept the first $X_i$ with
--   $$
--   X_i>\mathbb E[X^*]\cdot\theta\!\left(\frac{i-U}{n}\right),
--   $$
--   and accept $X_n$ if all earlier values are rejected. Then
--   $$
--   \mathbb E[\mathrm{ALG}]\ \ge\ 0.7419\cdot\mathbb E[X^*].
--   $$
--   The rule knows only $n$ and $\mathbb E[X^*]$, and $\theta$ is fixed before $n$ and the law. The guarantee is close to the full-information optimum $\beta^*\approx0.7454$ and well above the earlier mean-only guarantee $1-1/e$.
--
--   Differences from the source:
--   - generalization: a non-adaptive algorithm with a continuous concave decreasing threshold function → the randomly shifted rule of §3.4 with a threshold θ that is continuous, concave and strictly decreasing on [0,1], with θ(1) = 0 and θ(0) ≤ 1; reason: a narrower witness makes the ∃ stronger; the shifted rule is non-adaptive with threshold θ, the extra properties are §2's standing restriction (strictly decreasing to zero) and θ(0) = ∫b ≤ 1, and this is what Theorem 3.5 proves
--   - encoding: i.i.d. nonnegative random variables (§2) → a probability law μ on ℝ with μ((−∞,0)) = 0 and the product law Measure.pi; reason: same instances
--   - encoding: the algorithm knows E[X*] (finite) → Integrable id μ; reason: E[X*] < ∞ exactly when μ has a finite mean; it excludes only the case where the rule's input is undefined
--   - encoding: for every n → every n with NeZero n (n ≥ 1); reason: n counts the values
--   - encoding: arrivals i = 1, …, n, σ_i = (i − U)/n → 0-based j : Fin n with σ = ((j+1) − U)/n, U uniform on [0,1] via volume.restrict (Icc 0 1); reason: same rule
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Theorem 1.1, p.1 (PDF p.2); algorithm of §3.4, p.11 (PDF p.12) and Theorem 3.5

import Mathlib
import Definitions.Def_MeanOnlyProphet_expectedReward

open MeasureTheory

namespace MeanOnlyProphet

/-- **Theorem 1.1.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), Theorem 1.1, p.1 (PDF p.2): "There is a non-adaptive algorithm with a
continuous concave decreasing threshold function for i.i.d. variables such that, for every n, E[ALG] ≥
0.7419 · E[X∗]." The algorithm of the proof is the randomly shifted threshold rule of §3.4, p.11 (PDF
p.12) and Theorem 3.5.

There is one threshold `θ`, continuous, concave and strictly decreasing on `[0,1]` with `θ(1) = 0` and
`θ(0) ≤ 1`, such that for every `n ≥ 1` and every law `μ` of nonnegative values with finite mean, the
randomly shifted rule (draw `U` uniform on `[0,1]`, accept the first `X_i > E[X*] · θ((i − U)/n)`, else
accept `X_n`) earns `E[ALG] ≥ 0.7419 · E[X*]`.

**Formalization Note.** `θ` is chosen before `n` and `μ`; the rule depends on `μ` only through
`E[X*] = prophetMean μ n`. Sample space `(Fin n → ℝ) × ℝ` with `Measure.pi` of `μ` times uniform `U`;
0-based arrivals `j ↔ i = j + 1`, `σ = ((j+1) − U)/n`; strict acceptance; the last arrival is forced.
Finite mean is `Integrable id μ`; nonnegativity is `μ((−∞,0)) = 0`. `0.7419` is an exact decimal in `ℝ`. -/
theorem theorem_1_1 :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Set.Icc 0 1) ∧ ConcaveOn ℝ (Set.Icc 0 1) θ ∧
      StrictAntiOn θ (Set.Icc 0 1) ∧ θ 1 = 0 ∧ θ 0 ≤ 1 ∧
      ∀ (n : ℕ) [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ],
        μ (Set.Iio 0) = 0 → Integrable id μ →
          (0.7419 : ℝ) * prophetMean μ n ≤ expectedReward θ μ n := by sorry

end MeanOnlyProphet
