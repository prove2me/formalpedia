-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_3
-- name    : MeanOnlyProphet.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:24.918218+00:00
-- url     : https://prove2.me/theorems/2d92d9c9-cb3a-41dd-ac44-bd4cf5c0c07d
-- title:
--   Lemma A.3 — $\mathbb P(\mathrm{ALG}>\theta(t))=T_n(t)$
-- statement:
--   Let $\theta$ be continuous and strictly decreasing on $[0,1]$ with $\theta(1)=0$, let $n\ge1$, and let $X_1,\dots,X_n$ be i.i.d. nonnegative with law $\mu$ and CDF $F$. Run the randomly shifted rule with thresholds $\theta(\sigma_i)$, $\sigma_i=(i-U)/n$: accept the first $X_i>\theta(\sigma_i)$, else $X_n$. With the rate $r(t)=-n\log F(\theta(t))$ and $P$, $\overline P$, $A_P$ built from it, for every $t\in[0,1]$
--   $$
--   \mathbb P(\mathrm{ALG}>\theta(t))=T_n(t)=\begin{cases}1-\overline P(t)+n\big(1-e^{-r(t)/n}\big)A_P(t), & 0\le t\le 1-\frac1n,\\[2pt] 1-e^{-r(t)/n}\,\overline P(1-\frac1n), & 1-\frac1n<t\le1.\end{cases}
--   $$
--   It is the exact tail formula for the reward that turns the finite-$n$ expected reward into the functional $J_n$.
--
--   Differences from the source:
--   - generalization: the rule of App. A.2 for the forty-slope θ (θ(0) ≤ 1) under the normalization E[X*] = 1, i.e. thresholds θ(σ_i) → thresholds θ(σ_i) (scale 1) for every θ continuous and strictly decreasing to 0 on [0,1] (§2's class) and every nonnegative law, with no assumption on E[X*] or θ(0); reason: the proof uses neither E[X*] = 1 nor θ(0) ≤ 1, only that θ is continuous and strictly decreasing; when E[X*] = 1 the rule with thresholds E[X*]·θ(σ_i) is this rule, so the statement specializes to the source's
--   - encoding: P(ALG > θ(t)) → the sampleMeasure of {θ t < reward θ 1 n x u}, as a real number; reason: values then U; 0-based arrivals j ↔ i = j + 1
--   - encoding: r(t) = −n · log F(θ(t)), log 0 = −∞ → rateOf μ n θ : ℝ → ℝ≥0∞, equal to +∞ where F(θ(t)) = 0; reason: e^{−∞} = 0 makes F(θ(t)) = e^{−r(t)/n} hold also where F(θ(t)) = 0
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.3, p.29 (PDF p.30)

import Mathlib
import Definitions.Def_MeanOnlyProphet_expectedReward
import Definitions.Def_MeanOnlyProphet_rateOf
import Definitions.Def_MeanOnlyProphet_Tn

open MeasureTheory

namespace MeanOnlyProphet

/-- **Lemma A.3.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), Lemma A.3, p.29 (PDF p.30): "We have P(ALG > θ(t)) = Tn (t), where Tn (t) =
1 − P̄(t) + n · (1 − e^{−r(t)/n}) · AP (t), 0 ≤ t ≤ 1 − 1/n, Tn (t) = 1 − e^{−r(t)/n} · P̄(1 − 1/n),
1 − 1/n < t ≤ 1."

For a threshold `θ` that is continuous and strictly decreasing on `[0,1]` with `θ(1) = 0`, `n ≥ 1`
i.i.d. nonnegative values with law `μ` and CDF `F`, and `t ∈ [0,1]`: under the randomly shifted rule that
accepts the first `X_i > θ((i − U)/n)` and otherwise `X_n`, the probability that the accepted value
exceeds `θ(t)` is `T_n(t)` computed from the rate `r(t) = −n · log F(θ(t))`.

**Formalization Note.** App. A.2 states the rule under the normalization `E[X*] = 1`, so its thresholds
are `θ(σ_i)`; here the scale is `1` (`reward θ 1 n`) and no assumption on `E[X*]` is made. The
probability is the `sampleMeasure` of the event, converted to `ℝ`. Indices are 0-based with
`σ = ((j+1) − U)/n`; the rate is `ℝ≥0∞`-valued (`+∞` where `F(θ(t)) = 0`). -/
theorem lemma_A_3 (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1))
    (hθa : StrictAntiOn θ (Set.Icc 0 1)) (hθ1 : θ 1 = 0)
    (n : ℕ) [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (sampleMeasure μ n {p | θ t < reward θ 1 n p.1 p.2}).toReal = Tn n (rateOf μ n θ) t := by sorry

end MeanOnlyProphet
