-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_ban_value
-- name    : MarketplaceLeakage.Communication.ban_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:35.121554+00:00
-- url     : https://prove2.me/theorems/7d2b0699-ffd5-4ed1-b67a-bc3820929a2d
-- title:
--   p. 15 — the marketplace's profit after banning communication is max{Π_H(η), Π_L(η)}
-- statement:
--   Let $0<v$, $c<v$, $0<q<1$ and $0\le\eta<1$. In the communication-ban game, where the seller picks the more profitable of its two price options (ties to the low price), lists when that option pays at least zero, and the marketplace chooses any fee $f\in\mathbb R$, the marketplace's maximal revenue exists and equals
--   $$\max\{\Pi_H(\eta),\Pi_L(\eta)\},\qquad \Pi_H(\eta)=\eta q(v-c),\quad \Pi_L(\eta)=(1-\eta+\eta q)\Bigl(\frac{(1-(2-q)\eta)qv}{1-\eta}-c\Bigr).$$
--   $\Pi_H$ is attained at the fee $f=v-c$ (high-price option) and $\Pi_L$ at the threshold fee $f=\frac{(1-(2-q)\eta)qv}{1-\eta}-c$ (low-price option).
--
--   This is the profit with which the marketplace's ban decision in Proposition 3 is compared to the profit $q\Pi^*$ with communication allowed.
--
--   **Formalization Note.** The hypothesis $v>0$ is not on the page. It is necessary: for $v\le 0$ the threshold fee can exceed $qv-c$, the seller then refuses to list at the low price, and the maximum is smaller (e.g. $v=-0.8$, $c=-0.97$, $q=0.19$, $\eta=0.43$). It holds whenever $c\ge 0$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 15, §5.2, items 1–2 and "Thus, M's profit after banning communication is max {Π_H (η), Π_L (η)}"

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

namespace MarketplaceLeakage.Communication

theorem ban_value (v c : ℝ) (hvc : c < v) (hv : 0 < v) (q η : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    IsBanValue v c q η (max (PiH v c q η) (PiL v c q η)) := by sorry

end MarketplaceLeakage.Communication
