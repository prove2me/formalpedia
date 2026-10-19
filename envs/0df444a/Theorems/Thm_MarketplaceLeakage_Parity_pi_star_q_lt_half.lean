-- Prove2me | Theorems.Thm_MarketplaceLeakage_Parity_pi_star_q_lt_half
-- name    : MarketplaceLeakage.Parity.pi_star_q_lt_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:22.459666+00:00
-- url     : https://prove2.me/theorems/abe66de8-cfd2-4aa2-9bee-b546dcefd54d
-- title:
--   Proof of Proposition 4, p. 39 — for q < 1/2 the marketplace's profit without a PPC is (v − c)(1 − q min{(v − c)/(2μ), 1})
-- statement:
--   Let $c<v$, $\mu>0$ and $0<q<\tfrac12$, and let $G$ be the uniform switching-cost distribution on $[0,\mu]$. Without a price-parity clause the seller always lists; in the baseline state (probability $q$) it sets a seller-optimal direct price $p_d^*(f)$, and in the no-switching state every buyer buys on the marketplace. Then the marketplace's optimal expected profit over fees $f\le v-c$ is
--   $$\Pi^*=\max_{f\le v-c} f\big(1-q\,G(v-p_d^*(f))\big)=(v-c)\Big(1-q\min\Big\{\frac{v-c}{2\mu},1\Big\}\Big).$$
--
--   For $q<1/2$ the marketplace therefore charges the highest fee $f=v-c$; this is the other side of the comparison in Proposition 4.
--
--   **Formalization Note.** $\Pi^*$ is the `IsNoPPCValue` predicate of the setting file: the greatest of $f(1-qG(v-p_d))$ over pairs with $f\le v-c$ and $p_d$ seller-optimal at $f$, attained. The paper's formula for $q\ge 1/2$ on the same page is not posed (it omits the corner $f=v-c$).
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 39, §8.5, Proof of Proposition 4 (case q < 1/2, display Π*)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Parity_Setting

namespace MarketplaceLeakage.Parity

theorem pi_star_q_lt_half (v c μ q : ℝ) (hvc : c < v) (hμ : 0 < μ) (hq0 : 0 < q)
    (hq : q < 1 / 2) :
    IsNoPPCValue v c μ q ((v - c) * (1 - q * min ((v - c) / (2 * μ)) 1)) := by sorry

end MarketplaceLeakage.Parity
