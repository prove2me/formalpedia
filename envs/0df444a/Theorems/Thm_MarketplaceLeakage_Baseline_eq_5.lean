-- Prove2me | Theorems.Thm_MarketplaceLeakage_Baseline_eq_5
-- name    : MarketplaceLeakage.Baseline.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:34.264029+00:00
-- url     : https://prove2.me/theorems/984d171c-f401-4206-ae8c-5fe1295d9afb
-- title:
--   (5), p. 9 — the marketplace's profit at fee f ≥ 0 is f(1 − f/(2μ)) if f ≤ 2μ and 0 if f ≥ 2μ
-- statement:
--   In the baseline leakage game (value $v$, cost $c<v$, switching costs uniform on $[0,\mu]$, $\mu>0$), let $f\ge0$ be a fee and let $p_d$ be a seller-optimal direct price at $f$. Then the marketplace's profit $\Pi=f\,(1-G(v-p_d))$ equals
--   $$\Pi(f)=\begin{cases}0 & \text{if } f\ge 2\mu,\\ f\Bigl(1-\dfrac{f}{2\mu}\Bigr) & \text{if } f\le 2\mu.\end{cases}$$
--
--   This reduces the marketplace's problem to a one-dimensional maximization: at fees of $2\mu$ or more every buyer leaks to the direct channel and the marketplace earns nothing, and below $2\mu$ it keeps a share $1-f/(2\mu)$ of transactions.
--
--   **Formalization Note.** As with (4), the statement is posed for $f\ge 0$ rather than under the page's "Assuming $f\le v-c$". The two branches agree at $f=2\mu$. The standing assumption $c<v$ is kept as a hypothesis.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89cc00…3c98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 9, display (5)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

namespace MarketplaceLeakage.Baseline

/-- (5), p. 9: for `μ > 0`, a fee `f ≥ 0` and an optimal direct price `pd` of the seller at
`f`, the marketplace's profit is `0` if `f ≥ 2μ` and `f (1 − f/(2μ))` if `f ≤ 2μ`. -/
theorem eq_5 (v c μ : ℝ) (hvc : c < v) (hμ : 0 < μ) (f pd : ℝ) (hf : 0 ≤ f)
    (hpd : IsSOpt v c μ f pd) :
    MProfit v μ f pd = (if 2 * μ ≤ f then 0 else f * (1 - f / (2 * μ))) := by sorry

end MarketplaceLeakage.Baseline
