-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_fixed_price_ratio_bound
-- name    : GVRPricing.FixedPrice.fixed_price_ratio_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:04:06.646315+00:00
-- url     : https://prove2.me/theorems/bc8f6dd9-69b5-4272-b5b2-638f6fddd957
-- title:
--   Theorem 3 — J^OFP/J* ≥ J^FP/J* ≥ 1 − 1/(2√min{n, λ*t})
-- statement:
--   Let $\lambda(p)$ be a regular demand function with least revenue maximizer $\lambda^*>0$, let $n\ge1$ be the initial stock and $t>0$ the horizon. Let $J^*(n,t)$ be the optimal expected revenue over all non-anticipating pricing policies, $J^{FP}(n,t)$ the expected revenue of charging the fixed price $p^D=\max\{p^0,p^*\}$ (rate $\min\{\lambda^*,n/t\}$) throughout, and $J^{OFP}(n,t)$ the expected revenue of the best fixed price. Then $0<J^*(n,t)<\infty$ and
--   $$\frac{J^{OFP}(n,t)}{J^*(n,t)}\ \ge\ \frac{J^{FP}(n,t)}{J^*(n,t)}\ \ge\ 1-\frac{1}{2\sqrt{\min\{n,\lambda^*t\}}}.$$
--
--   A single fixed price is therefore asymptotically optimal when the volume of expected sales is large: when the stock is large and there is ample time to sell it ($n\gg1$, $n<\lambda^*t$), or when the potential sales at the revenue-maximizing price are large and the stock covers them ($\lambda^*t\gg1$, $n\ge\lambda^*t$). With 400 items and scarce stock the guarantee is 97.5%.
--
--   **Formalization Note** The hypotheses $n\ge1$, $t>0$ and $\lambda^*>0$ are implicit on the page: the ratios divide by $J^*(n,t)$, which vanishes when $n=0$, when $t=0$, or when $\lambda^*=0$ (then $r\equiv0$ on $\Lambda$). The conclusion asserts that $J^*(n,t)$ is finite and positive, so the real ratios are the paper's ratios and not default values. $J^{FP}$ and $J^{OFP}$ are expected revenues of constant-price policies of the stochastic model, not formulas.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1008 (PDF 10), §3.3, Theorem 3

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Theorem 3** (p. 1008). For a regular demand function with `λ* > 0`, a stock `n ≥ 1` and a
horizon `t > 0`, the optimal expected revenue `J*(n, t)` is finite and positive, and
`J^OFP(n, t)/J*(n, t) ≥ J^FP(n, t)/J*(n, t) ≥ 1 − 1/(2√min{n, λ* t})`. -/
theorem fixed_price_ratio_bound (M : Model) (n : ℕ) (t : ℝ) (hn : 1 ≤ n) (ht : 0 < t)
    (hl : 0 < M.lstar) :
    optValue M n t ≠ ∞ ∧ 0 < optValue M n t ∧
    (fpValue M n t).toReal / (optValue M n t).toReal ≤
      (ofpValue M n t).toReal / (optValue M n t).toReal ∧
    1 - 1 / (2 * Real.sqrt (min (n : ℝ) (M.lstar * t))) ≤
      (fpValue M n t).toReal / (optValue M n t).toReal := by sorry

end GVRPricing.FixedPrice
