-- Prove2me | Theorems.Thm_MarketMakerAds_theorem_1
-- name    : MarketMakerAds.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:39.505999+00:00
-- url     : https://prove2.me/theorems/ecdd5387-8d9e-4868-9451-a53b025c6ced
-- title:
--   Theorem 1 (Truthfulness Under Risk Aversion)
-- statement:
--   Consider one buyer with value $v$ in the $(I+1)$-th price auction under the mean-variance model with $\beta\ge0$ or the CARA model with $\alpha\ge0$. The clearing price $p$ is set by the other bidders and has law $h$, whatever their behaviour; the buyer's report $b$ only decides whether it wins: it wins when $p\in W$, with $W=\{p<b\}$ or $\{p\le b\}$, and then pays $p$. Let $U_{\mathrm{truth}}$ be the utility of the truthful payoff $(v-p)^+$ and $U_{\mathrm{lie}}$ the utility of reporting $b$. Assume the negative part of $p$ has a finite second moment. Then:
--
--   1. **Universal truthfulness.** For every realized clearing price $p$, reporting $v$ gives at least the utility of reporting $b$.
--   2. **Truthfulness in expectation, part 1.** If $U_{\mathrm{truth}}>0$, then $U_{\mathrm{truth}}\ge U_{\mathrm{lie}}$.
--   3. **Truthfulness in expectation, part 2.** If $U_{\mathrm{truth}}\le0$, then $U_{\mathrm{lie}}\le0$.
--
--   For mean-variance utility the utility over a distribution is not the expectation of the utilities of outcomes, so part 1 does not imply parts 2 and 3. This theorem justifies truthful bidding, so that the auction clearing price is the $(I+1)$-th highest value.
--
--   Differences from the source:
--   - generalization: a clearing-price density $h$ on $[0,\infty)$ → any probability law on $\mathbb R$ whose negative part has a finite second moment; reason: every law on $[0,\infty)$ satisfies the hypothesis.
--   - generalization: ties at $p=b$ not specified → either tie rule, win set $\{p<b\}$ or $\{p\le b\}$; reason: covers both deterministic tie rules; under a density they coincide.
--   - encoding: "universally truthful", i.e. truthful for each possible value of $v_{I+1}$ → the utility under the point-mass law at each $p$; reason: the utility of a single outcome is the utility of the point mass (p.12, below eq. (2)).
--   - encoding: the $(I+1)$-th price auction → one bidder facing a clearing-price law that its bid does not move; reason: this is the reduction the proof makes on p.30.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Theorem 1, p.14 (restated and proved in Appendix B, pp.30–34)

import Mathlib
import Definitions.Def_MarketMakerAds_riskUtility

open MeasureTheory

namespace MarketMakerAds

/-- **Theorem 1 (Truthfulness Under Risk Aversion), p.14.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Theorem 1, p.14
(restated p.30): "Under the CARA and Mean-variance utility models, the (I + 1)-th price auction
is both universally truthful and truthful in expectation. Let U_truth (resp. U_lie) be the
utility in the auction under truthful reporting (resp. mis-reporting). Then, 1. If U_truth > 0,
then U_truth ≥ U_lie. 2. If U_truth ≤ 0, then U_lie ≤ 0."

A buyer with value `v` reports `b`. Its bid does not move the clearing price `p`, whose law `h`
is induced by the other bidders' behaviour (p.30); it wins iff `p ∈ W` (`W = {p < b}` or
`{p ≤ b}`) and pays `p`. Then:
1. (universal truthfulness) for every realized clearing price `p` (the law `dirac p`), the
   truthful payoff gives at least the utility of the report `b`;
2. (truthfulness in expectation, part 1) if `U_truth > 0` then `U_lie ≤ U_truth`;
3. (part 2) if `U_truth ≤ 0` then `U_lie ≤ 0`.

**Formalization Note** Both models with the paper's range `β ≥ 0`, `α ≥ 0`. The law `h` is any
probability measure on `ℝ` whose negative part has a finite second moment (the paper's `h` is a
density on `[0, ∞)`), and both deterministic tie rules at `p = b` are covered. -/
theorem theorem_1 (m : RiskModel) (hm : m.IsNonneg) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hneg : Integrable (fun p => (max (-p) 0) ^ 2) h)
    (v b : ℝ) (W : Set ℝ) (hW₁ : Set.Iio b ⊆ W) (hW₂ : W ⊆ Set.Iic b) :
    let Xt : ℝ → ℝ := fun p => max (v - p) 0
    let Xl : ℝ → ℝ := W.indicator fun p => v - p
    (∀ p : ℝ, riskUtility m (Measure.dirac p) Xl ≤ riskUtility m (Measure.dirac p) Xt) ∧
    (0 < riskUtility m h Xt → riskUtility m h Xl ≤ riskUtility m h Xt) ∧
    (riskUtility m h Xt ≤ 0 → riskUtility m h Xl ≤ 0) := by sorry

end MarketMakerAds
