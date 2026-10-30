-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_ban_profit_is_max
-- name    : MarketplaceLeakage.Communication.ban_profit_is_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:03:28.585885+00:00
-- url     : https://prove2.me/theorems/c95c8a02-12b6-493b-b817-f877f1bb1d8d
-- title:
--   Under a ban, M's optimal fee earns $\max\{\Pi_H(\eta),\Pi_L(\eta)\}$
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Let $0<c<v$, $0<q<1$ and $0\le\eta<1$, and let $R(f)$ be the marketplace's revenue at fee $f$ given the seller's best response (high price iff strictly better; list iff the chosen profit is $\ge 0$). Then
--
--   1. at $f=v-c$ the seller strictly prefers the high price and $R(v-c)=\Pi_H(\eta)$;
--   2. at $f=\frac{(1-(2-q)\eta)qv}{1-\eta}-c$ the seller takes the low price and $R(f)=\Pi_L(\eta)$;
--   3. the greatest revenue over all fees is
--
--   $$
--   \max_{f\in\mathbb R} R(f)=\max\{\Pi_H(\eta),\Pi_L(\eta)\}.
--   $$
--
--   This is the marketplace's profit after banning communication, which Proposition 3 compares with $q\Pi^*$.
--
--   Differences from the source:
--
--   - encoding: Π_L(η) and the option-2 fee for η ≤ 1 → statements about them assume η < 1; reason: both divide by 1 − η and are undefined at η = 1; the condition only excludes the undefined case
--   - reading: "Otherwise, S chooses the second (low-price) option" and "Assuming S lists on M" → ties go to the low price; S lists iff the profit of its chosen option is ≥ 0 (outside option zero); reason: "Otherwise" is the page's tie rule; at the option-1 fee f = v − c the seller earns exactly zero, so it must list at zero profit for option 1 to earn Π_H
--   - reading: "two possible optimal options for M" and "M's profit after banning communication is max{Π_H(η), Π_L(η)}" → the revenue at f = v − c is Π_H, at the option-2 fee is Π_L, and max{Π_H, Π_L} is the greatest revenue over all real fees; reason: "optimal" read as the maximum of M's revenue over every fee
--   - encoding: the ban stage of the game → the seller's best response written into the closed-form revenue banRevenue; reason: the page's analysis consists of exactly these two pricing options; buyer behaviour enters through the demands ηq and 1 − η + ηq
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, unnumbered, p. 15

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_highPriceThreshold
import Definitions.Def_MarketplaceLeakage_Communication_banProfit
import Definitions.Def_MarketplaceLeakage_Communication_banRevenue

namespace MarketplaceLeakage.Communication

/-- **Under a ban, the marketplace's optimal fee earns `max{Π_H(η), Π_L(η)}`.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, unnumbered, p. 15: "In turn, this implies that there are two possible optimal
options for M when choosing f: 1. Set f = v − c, which induces S to choose the high-price
option, resulting in M making a profit of ΠH (η) = ηq (v − c). 2. Set
f = (1−(2−q)η)qv/(1−η) − c, which induces S to choose the low-price option, resulting in M
making a profit of ΠL (η) = (1 − η + ηq) ((1−(2−q)η)qv/(1−η) − c). Thus, M's profit after
banning communication is max {ΠH (η) , ΠL (η)}".

Standing assumptions: `0 < c < v` (pp. 5–6), `0 < q < 1` (p. 14), `0 ≤ η` (p. 14). Then
(1) at `f = v − c` the seller takes the high price and the marketplace earns `Π_H(η)`;
(2) at `f = highPriceThreshold` the seller takes the low price and the marketplace earns
`Π_L(η)`; (3) `max{Π_H(η), Π_L(η)}` is the greatest revenue over all fees `f`.

**Formalization Note.** `η < 1` because `Π_L` and the threshold are undefined at `η = 1`.
Ties go to the low price and the seller lists iff its chosen profit is nonnegative (see
`banRevenue`). -/
theorem ban_profit_is_max {q v c η : ℝ} (hc : 0 < c) (hcv : c < v) (hq0 : 0 < q) (hq1 : q < 1)
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ((1 - η + η * q) * (q * v - c - (v - c)) < η * q * (v - c - (v - c)) ∧
        banRevenue q v c η (v - c) = piH q v c η) ∧
      (¬ ((1 - η + η * q) * (q * v - c - highPriceThreshold q v c η) <
            η * q * (v - c - highPriceThreshold q v c η)) ∧
        banRevenue q v c η (highPriceThreshold q v c η) = piL q v c η) ∧
      IsGreatest (Set.range (banRevenue q v c η)) (banProfit q v c η) := by sorry

end MarketplaceLeakage.Communication
