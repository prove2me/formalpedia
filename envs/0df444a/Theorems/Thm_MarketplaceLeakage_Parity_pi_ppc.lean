-- Prove2me | Theorems.Thm_MarketplaceLeakage_Parity_pi_ppc
-- name    : MarketplaceLeakage.Parity.pi_ppc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:23.352042+00:00
-- url     : https://prove2.me/theorems/36fa005d-5fa7-4719-9f74-311bc8c4a3f7
-- title:
--   Π*_PPC, p. 23 — under a PPC the marketplace's profit is max{v − c − max_{c≤p_d≤v}(p_d − c)G(v − p_d), (1 − q)(v − c)}
-- statement:
--   Let $c<v$, $\mu>0$ and $0<q\le1$, and let $G$ be the uniform switching-cost distribution on $[0,\mu]$. Write
--   $$D=\max_{c\le p_d\le v}\,(p_d-c)\,G(v-p_d)$$
--   for the seller's best delisting payoff in the baseline state. Then this maximum exists, and for it the marketplace's optimal expected profit under a price-parity clause, maximizing over all fees $f\in\mathbb R$, is
--   $$\Pi^*_{PPC}=\max\big\{\,v-c-D,\ (1-q)(v-c)\,\big\}.$$
--
--   The two terms are the two candidate fees of the paper: $f=v-c$, at which the seller accepts only in the no-switching state, and $f=v-c-D$, at which it always accepts. The result reduces the marketplace's choice under a PPC to these two corners, and it is one of the two sides compared in Proposition 4.
--
--   **Formalization Note.** $\Pi^*_{PPC}$ is the `IsPPCValue` predicate of the setting file: the stated number is the greatest expected revenue over all real fees, and it is attained. The existence of $D$ is part of the conclusion. The paper states this display for a general $G$; here it is posed for the uniform $G$ of Proposition 4. The hypothesis $q>0$ is the mission's standing assumption (the statement also holds at $q=0$).
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 23, §5.4, display Π*_PPC

import Mathlib
import Definitions.Def_MarketplaceLeakage_Parity_Setting

namespace MarketplaceLeakage.Parity

theorem pi_ppc (v c μ q : ℝ) (hvc : c < v) (hμ : 0 < μ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∃ D, IsGreatest ((fun pd => delistPayoff v c μ pd) '' Set.Icc c v) D) ∧
    ∀ D, IsGreatest ((fun pd => delistPayoff v c μ pd) '' Set.Icc c v) D →
      IsPPCValue v c μ q (max (v - c - D) ((1 - q) * (v - c))) := by sorry

end MarketplaceLeakage.Parity
