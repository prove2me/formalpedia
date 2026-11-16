-- Prove2me | Theorems.Thm_MeanOnlyProphet_Supplement_theorem_3_5
-- name    : MeanOnlyProphet.Supplement.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:28:49.386839+00:00
-- url     : https://prove2.me/theorems/5ba562b0-18d5-4db2-8a25-723387750f78
-- title:
--   Theorem 3.5 — the forty-slope threshold earns $0.7419\,\mathbb E[X^*]$ for every $n$
-- statement:
--   There are forty positive nondecreasing slopes $b_1\le\dots\le b_{40}$ with the following properties. Let $b$ be the step drop rate equal to $b_k$ on the $k$-th of forty equal subintervals of $[0,1]$, and let $\theta(t)=\int_t^1b(s)\,ds$. The slopes carry the certified facts of §3.3:
--   1. $0.74196156\le\theta(0)<0.74196157$;
--   2. $b_{40}<1.81532$;
--   3. $L(b,q)\ge0.74190517$ for every rate $q$ that is nonnegative and nondecreasing on $[0,1]$.
--
--   For this $\theta$, every $n\ge1$ and every law of nonnegative i.i.d. values $X_1,\dots,X_n$ with finite mean, run the **randomly shifted threshold rule**: draw $U$ uniform on $[0,1]$, accept the first $X_i>\mathbb E[X^*]\cdot\theta\big((i-U)/n\big)$, and accept $X_n$ if all earlier values are rejected. Then
--   $$
--   \mathbb E[\mathrm{ALG}]\ \ge\ 0.7419\cdot\mathbb E[X^*].
--   $$
--   This is the finite-$n$ guarantee for the specific threshold built in §3.3, and it implies Theorem 1.1.
--
--   **Formalization Note** The functional $L(b,q)$ is the published `MeanOnlyProphet.Lfun`, with a real rate entering through `toRate`. The rule is the published `MeanOnlyProphet.expectedReward`.
--
--   Differences from the source:
--   - reading: the forty-slope threshold θ constructed above (§3.3) → ∃ forty positive nondecreasing slopes carrying §3.3's certified facts (0.74196156 ≤ θ(0) < 0.74196157, b₄₀ < 1.81532, L(b, q) ≥ 0.74190517 for every nonnegative nondecreasing q); reason: the slopes are certificate data and are not printed; these are the facts by which the paper identifies them, as in the published certified_bound_3_3
--   - encoding: competitive ratio under the normalization E[X*] = 1 (§2) → all laws, with the threshold scaled by E[X*]; reason: the theorem's display is E[ALG] ≥ 0.7419 · E[X*]; the rule is scale invariant
--   - encoding: the algorithm knows E[X*] (finite) → Integrable id μ; reason: E[X*] < ∞ exactly when μ has a finite mean
--   - encoding: b_1, …, b_40 and arrivals i = 1, …, n → 0-based bs : Fin 40 → ℝ and j : Fin n with σ = ((j+1) − U)/n; reason: same objects
--   - encoding: for every n → every n with NeZero n (n ≥ 1); reason: n counts the values
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Theorem 3.5, p.11 (PDF p.12); §3.3, pp.10–11 (PDF pp.11–12); App. A.2, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_MeanOnlyProphet_expectedReward
import Definitions.Def_MeanOnlyProphet_Lfun

open MeasureTheory

namespace MeanOnlyProphet.Supplement

/-- **Theorem 3.5 (the forty-slope threshold, randomly shifted rule, every n).** Feng, Jin, Wu, Xiang,
*Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), Theorem 3.5, p.11
(PDF p.12): "Using the randomly shifted threshold rule with the forty-slope threshold θ constructed
above, we have E[ALG] ≥ 0.7419 · E[X∗] for every n." The threshold is the one of §3.3, p.11 (PDF
p.12): "We use N = 40 positive nondecreasing drop rates obtained by this search. … γ = 0.74190517 . . . ,
and θ(0) = 0.74196156 . . . ." and App. A.2, p.30 (PDF p.31): "θ(0) < 0.741962 and b40 < 1.81532".

There are forty positive nondecreasing slopes `b_1 ≤ ⋯ ≤ b_40` with the certified properties of §3.3
(`θ(0) = 0.74196156…`, `b_40 < 1.81532`, `L(b, q) ≥ 0.74190517` for every nonnegative nondecreasing
rate `q`) such that, for `θ(t) = ∫_t^1 b`, the randomly shifted rule earns `E[ALG] ≥ 0.7419 · E[X*]` for
every `n ≥ 1` and every law of nonnegative i.i.d. values with finite mean.

**Formalization Note.** The slopes are not printed (they are certificate data), so they are
existential, identified by the same certified facts as the published
`MeanOnlyProphet.certified_bound_3_3`. `bs : Fin 40 → ℝ` is 0-based (`bs 39` is `b_40`);
`θ = thetaOf (stepRate bs)`. The rule is the published `MeanOnlyProphet.expectedReward` (shift `U`
uniform on `[0,1]`, strict acceptance against `E[X*] · θ((i − U)/n)`, last value forced). -/
theorem theorem_3_5 :
    ∃ bs : Fin 40 → ℝ, (∀ i, 0 < bs i) ∧ Monotone bs ∧
      0.74196156 ≤ thetaOf (stepRate bs) 0 ∧ thetaOf (stepRate bs) 0 < 0.74196157 ∧
      bs 39 < 1.81532 ∧
      (∀ q : ℝ → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q t) → MonotoneOn q (Set.Icc 0 1) →
        (0.74190517 : ℝ) ≤ Lfun (stepRate bs) (toRate q)) ∧
      ∀ (n : ℕ) [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ],
        μ (Set.Iio 0) = 0 → Integrable id μ →
          (0.7419 : ℝ) * prophetMean μ n ≤ expectedReward (thetaOf (stepRate bs)) μ n := by sorry

end MeanOnlyProphet.Supplement
