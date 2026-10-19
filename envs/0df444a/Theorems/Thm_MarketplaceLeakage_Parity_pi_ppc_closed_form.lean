-- Prove2me | Theorems.Thm_MarketplaceLeakage_Parity_pi_ppc_closed_form
-- name    : MarketplaceLeakage.Parity.pi_ppc_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:21.171553+00:00
-- url     : https://prove2.me/theorems/81a06636-d9b8-4473-bfe9-0a1c04770d1e
-- title:
--   Proof of Proposition 4, p. 39 — the delisting payoff is (v − c)^2/(4μ) or v − c − μ, and Π*_PPC in closed form
-- statement:
--   Let $c<v$, $\mu>0$ and $0<q\le1$, and let $G$ be the uniform switching-cost distribution on $[0,\mu]$. Then the seller's best delisting payoff in the baseline state is
--   $$\max_{c\le p_d\le v}\,(p_d-c)\,G(v-p_d)=D_\mu:=\begin{cases}\dfrac{(v-c)^2}{4\mu}&\text{if }\mu\ge\dfrac{v-c}{2},\\[2mm] v-c-\mu&\text{if }\mu<\dfrac{v-c}{2},\end{cases}$$
--   and the marketplace's optimal expected profit under a price-parity clause is
--   $$\Pi^*_{PPC}=\max\big\{\,v-c-D_\mu,\ (1-q)(v-c)\,\big\}.$$
--
--   This is the closed form of $\Pi^*_{PPC}$ used in the comparison of Proposition 4. The two cases of $D_\mu$ agree at $\mu=(v-c)/2$.
--
--   **Formalization Note.** The maximum is asserted with `IsGreatest` over the image of $[c,v]$, and $\Pi^*_{PPC}$ by the `IsPPCValue` predicate (greatest expected revenue over all real fees, attained). The paper prints the same display under "If $q\ge 1/2$" and under "If $q<1/2$"; it does not depend on $q$, so it is posed for every $q\in(0,1]$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 39, §8.5, Proof of Proposition 4 (display Π*_PPC)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Parity_Setting

namespace MarketplaceLeakage.Parity

theorem pi_ppc_closed_form (v c μ q : ℝ) (hvc : c < v) (hμ : 0 < μ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    IsGreatest ((fun pd => delistPayoff v c μ pd) '' Set.Icc c v)
      (if (v - c) / 2 ≤ μ then (v - c) ^ 2 / (4 * μ) else v - c - μ) ∧
    IsPPCValue v c μ q
      (max (v - c - (if (v - c) / 2 ≤ μ then (v - c) ^ 2 / (4 * μ) else v - c - μ))
        ((1 - q) * (v - c))) := by sorry

end MarketplaceLeakage.Parity
