-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_proposition_3
-- name    : MarketplaceLeakage.Communication.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:27.44957+00:00
-- url     : https://prove2.me/theorems/7891e77b-001c-4c3c-b88f-4c17b7f3ac89
-- title:
--   Proposition 3, pp. 15–16 — the marketplace bans communication above Π*/(v − c), below η_L when q > c/(v − Π*), always when q is near one, and for small (not large) μ
-- statement:
--   A marketplace $M$ hosts a seller of a product with value $v$ and cost $c<v$. Each buyer values the product at $v$ with probability $q\in(0,1)$, and $0$ otherwise. If $M$ allows buyer–seller communication, its expected profit is $q\Pi^*$, where $\Pi^*$ is its baseline profit, with $0<\Pi^*<v-c$. If it bans communication, leakage disappears but a buyer learns their valuation only with probability $\eta\in[0,1]$, and $M$ earns its *ban value* $V(\eta)$, the maximal revenue of the ban game. $M$ *prefers to ban* when $V(\eta)>q\Pi^*$ and *prefers to allow* when $V(\eta)<q\Pi^*$. Write $\Pi_L(\eta)=(1-\eta+\eta q)\bigl(\frac{(1-(2-q)\eta)qv}{1-\eta}-c\bigr)$.
--
--   **Proposition 3.**
--   1. For every $\Pi^*\in(0,v-c)$, $M$ prefers to ban for all $\eta$ with
--   $$\frac{\Pi^*}{v-c}<\eta\le 1 .$$
--   2. If $q>\frac{c}{v-\Pi^*}$, there is a unique $\eta_L\in[0,1)$ with $\Pi_L(\eta_L)=q\Pi^*$; moreover $\eta_L>0$ and $M$ prefers to ban for every $\eta\in[0,\eta_L)$.
--   3. For every $\Pi^*\in(0,v-c)$ there is $q_0<1$ such that, for all $q\in(q_0,1)$, $M$ prefers to ban for every $\eta\in[0,1]$.
--   4. Suppose $c\ge 0$, the switching costs are uniform on $[0,\mu]$, and $\Pi^*=\Pi^*(\mu)$ is the baseline equilibrium profit. For each fixed $q\in(0,1)$ and $\eta\in(0,1)$ there is $\mu_0>0$ such that $M$ prefers to ban whenever $0<\mu<\mu_0$, and there is $\mu_1$ such that $M$ prefers to allow whenever $\mu>\mu_1$.
--
--   The proposition describes when a marketplace should give up buyer–seller communication to stop leakage: when the information loss is small, when it is so large that the low-price option is attractive, and always when buyers are a priori likely to value the product.
--
--   **Formalization Note.** In parts 1–3, $\Pi^*$ is any real number in $(0,v-c)$ rather than the baseline profit under a general distribution $G$, whose regularity the paper does not pin down; the proof on p. 38 uses only $0<\Pi^*<v-c$, so this is a disclosed generalization. Part 4 pins $\Pi^*$ down as the equilibrium profit of the baseline game with the clamped uniform CDF. Part 4 is stated for each fixed $\eta\in(0,1)$ (the threshold may depend on $\eta$): at $\eta=0$ with $qv\le c$ banning fails for small $\mu$, and at $\eta=1$ allowing fails for large $\mu$. Part 4 also adds $c\ge 0$, not stated in the paper: for $c<0$ and small $\eta>0$ the marketplace bans for every $\mu$. Part 2 characterizes $\eta_L$ on $[0,1)$ because $\Pi_L$ is undefined at $\eta=1$. The ban value is computed from the ban game, not from the formula $\max\{\Pi_H,\Pi_L\}$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), pp. 15–16, Proposition 3; proof §8.4, p. 38; Π*(μ) from (6), p. 10

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

namespace MarketplaceLeakage.Communication

theorem proposition_3 (v c : ℝ) (hvc : c < v) :
    -- (i) ban for every η > Π*/(v − c), η ≤ 1
    (∀ q PiStar η : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c →
      PiStar / (v - c) < η → η ≤ 1 → PrefersBan v c q η PiStar) ∧
    -- (ii) if q > c/(v − Π*): η_L ∈ [0, 1) with Π_L(η_L) = qΠ* exists and is unique ...
    (∀ q PiStar : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c → c / (v - PiStar) < q →
      ∃! ηL : ℝ, 0 ≤ ηL ∧ ηL < 1 ∧ PiL v c q ηL = q * PiStar) ∧
    -- ... it is positive, and the marketplace bans for every η ∈ [0, η_L)
    (∀ q PiStar ηL η : ℝ, 0 < q → q < 1 → 0 < PiStar → PiStar < v - c →
      c / (v - PiStar) < q → 0 ≤ ηL → ηL < 1 → PiL v c q ηL = q * PiStar →
      0 < ηL ∧ (0 ≤ η → η < ηL → PrefersBan v c q η PiStar)) ∧
    -- (iii) for q close enough to one, ban for every η ∈ [0, 1]
    (∀ PiStar : ℝ, 0 < PiStar → PiStar < v - c →
      ∃ q₀ < 1, ∀ q η : ℝ, q₀ < q → q < 1 → 0 ≤ η → η ≤ 1 → PrefersBan v c q η PiStar) ∧
    -- (iv) uniform MarketplaceLeakage.Baseline.G, for each fixed η ∈ (0, 1), with the disclosed addition c ≥ 0
    (0 ≤ c → ∀ q η : ℝ, 0 < q → q < 1 → 0 < η → η < 1 →
      (∃ μ₀ > 0, ∀ μ P : ℝ, 0 < μ → μ < μ₀ → IsBaselineValue v c μ P → PrefersBan v c q η P) ∧
      (∃ μ₁ : ℝ, ∀ μ P : ℝ, μ₁ < μ → IsBaselineValue v c μ P → PrefersAllow v c q η P)) := by sorry

end MarketplaceLeakage.Communication
