-- Prove2me | Theorems.Thm_GreedyReusableNet_threshold_average
-- name    : GreedyReusableNet.threshold_average
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:33:47.263187+00:00
-- url     : https://prove2.me/theorems/33638363-6491-4c11-9d47-b4a4828ff14b
-- title:
--   p.42 — $\mathbb E_r[r\mathbb 1\{x\ge r\}]=x/(1+\ln R)$ for $r\sim G$
-- statement:
--   Let $0<a\le b$ and let $r$ be drawn from the threshold law $G(x)=(1+\ln(x/a))/(1+\ln(b/a))$ on $[a,b]$. For every $x\in[a,b]$,
--   $$\mathbb E\big[r\,\mathbb 1\{r\le x\}\big]=\frac{a}{1+\ln(b/a)}+\int_a^x\frac{r\cdot 1/r}{1+\ln(b/a)}\,dr=\frac{x}{1+\ln(b/a)}.$$
--   With $a=r_{\min}$, $b=r_{\max}$ this is the averaging step of the proof of Theorem 2 that turns OPT's thresholded reward into $r_t(B;n^{\mathrm{OPT}}_t(B))/(1+\ln R)$; with $\bar r_{\min},\bar r_{\max}$ it is the same step for (6).
--
--   Differences from the source:
--   - reading: the bracket r_min/(1 + ln R) + ∫_{r_min}^{x} (r·1/r)/(1 + ln R) applied with x = r_t(B; n^OPT_t(B)) → the identity for x ∈ [r_min, r_max]; reason: the bracket equals E_r[r𝟙{x ≥ r}] exactly on [r_min, r_max], where positive rewards lie; zero rewards contribute 0 to both sides of the chain
--   - encoding: the law with distribution function G(x) = (1 + ln(x/r_min))/(1 + ln R) on [r_min, r_max] → thresholdLaw a b = atom 1/(1 + ln(b/a)) at a plus density 1/((1 + ln(b/a)) x) on (a, b]; reason: the same law: the verification file proves it is a probability measure with distribution function G on [a, b]
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, proof of Theorem 2, p.42, fourth line of the final chain (and p.43)

import Mathlib
import Definitions.Def_GreedyReusableNet_thresholdLaw

open MeasureTheory

namespace GreedyReusableNet

/-- **The threshold average** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, proof of Theorem 2, p.42,
fourth line of the final chain; the same for `Ḡ` on p.43):
`𝔼_r[r 𝟙{x ≥ r}] = r_min/(1 + ln R) + ∫_{r_min}^{x} (r · 1/r)/(1 + ln R) dr = x/(1 + ln R)`
for `r ∼ G` and `x ∈ [r_min, r_max]`, `R = r_max/r_min`.

For `0 < a ≤ b` and `a ≤ x ≤ b`, with `r` drawn from `thresholdLaw a b`:
`𝔼[r 𝟙{r ≤ x}] = x/(1 + ln(b/a))`. -/
theorem threshold_average (a b x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hax : a ≤ x) (hxb : x ≤ b) :
    ∫ r, (if r ≤ x then r else 0) ∂(thresholdLaw a b) = x / (1 + Real.log (b / a)) := by sorry

end GreedyReusableNet
