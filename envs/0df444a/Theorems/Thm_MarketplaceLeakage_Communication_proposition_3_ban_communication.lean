-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_proposition_3_ban_communication
-- name    : MarketplaceLeakage.Communication.proposition_3_ban_communication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:36.379981+00:00
-- url     : https://prove2.me/theorems/d14f9994-0dac-4bbb-ac6e-11d6089b55ad
-- title:
--   Proposition 3: when the marketplace prefers to ban communication (corrected: (iv) needs $\eta>0$ or $qv>c$ for the ban part and $\eta<1$ for the allow part)
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Without a ban the marketplace earns $q\Pi^*$, where $\Pi^*$ is its baseline equilibrium profit, with $0<\Pi^*<v-c$. With a ban it earns $\max\{\Pi_H(\eta),\Pi_L(\eta)\}$, where $\Pi_H(\eta)=\eta q(v-c)$ and $\Pi_L(\eta)=(1-\eta+\eta q)\left(\frac{(1-(2-q)\eta)qv}{1-\eta}-c\right)$. "Prefers" means a strict comparison of these two profits.
--
--   Let $0<c<v$. For every $P$ with $0<P<v-c$ (in the role of $\Pi^*$):
--
--   1. **(i)** for every $q\in(0,1)$ and every $\eta$ with $\frac{P}{v-c}<\eta\le1$, the marketplace prefers to ban communication;
--   2. **(ii)** for every $q\in(0,1)$ with $q>\frac{c}{v-P}$ there is $\eta_L\in(0,1)$ with
--   $$
--   \Pi_L(\eta_L)=qP,
--   $$
--   which is the only solution of this equation in $[0,1)$, and the marketplace prefers to ban communication for every $\eta\in[0,\eta_L)$;
--   3. **(iii)** there is $q_0<1$ such that for every $q\in(q_0,1)$ and every $\eta\in[0,1]$ the marketplace prefers to ban communication.
--
--   Moreover, with uniform switching costs $G(s)=s/\mu$, $\bar s=\mu$, and $\Pi^*=\Pi^*(\mu)$ of (6), for every $q\in(0,1)$ and $\eta\in[0,1]$:
--
--   4. **(iv)** if $\eta>0$ or $qv>c$, there is $\mu_0>0$ such that the marketplace prefers to ban communication for every $\mu\in(0,\mu_0)$; and if $\eta<1$, there is $\mu_1$ such that it prefers to allow communication for every $\mu>\mu_1$.
--
--   The proposition describes when hiding buyer–seller contact pays: when little information is lost (high $\eta$), when almost all information is lost but the expected value $qv$ is high enough, and, for high enough $q$, always.
--
--   **Formalization Note** Clause (iv) carries two corrections of the printed statement, listed below with counterexamples. Lean's $x/0=0$ makes $\Pi_L(1)=-qc$, so the ban profit at $\eta=1$ is $q(v-c)$, as in the paper.
--
--   Differences from the source:
--
--   - reading: "positive marginal costs" (p. 6) and "v > c" (p. 5) → hypotheses 0 < c and c < v; reason: standing assumptions of the model; the allow part of (iv) fails at c = 0 (with η = 0 the ban profit is qv = q(v − c) ≥ qΠ*(µ) for every µ)
--   - generalization: Π* of (3), the baseline equilibrium profit for a switching-cost distribution G → in (i)–(iii), every real P with 0 < P < v − c; reason: Π* enters (i)–(iii) only through 0 < Π* < v − c (p. 8, p. 16), so the statement specializes to Π* for every admissible G
--   - encoding: the allow profit qΠ* and the ban profit max{Π_H(η), Π_L(η)} derived from the game (p. 15) → the closed forms q · P and banProfit; reason: Proposition 3 compares exactly these profits; the derivation of the ban profit is the milestone ban_profit_is_max; the baseline game is not formalized
--   - reading: "prefers to ban (allow)" → strict inequality between the ban profit and the allow profit; reason: the paper does not discuss ties; the strict reading is the stronger one on both sides
--   - reading: the ranges of q and η → 0 < q < 1 and 0 ≤ η ≤ 1 in every clause; reason: p. 14: "0 < q < 1" and "from one to η ≤ 1"; η = 0 is part of the model (p. 15)
--   - reading: the quantifier order → (i) for all q and all η ∈ (P/(v − c), 1]; (ii) for each q some η_L; (iii) one q₀ < 1, depending on v, c, P, for all η ∈ [0, 1]; (iv) µ₀ > 0 and µ₁ depending on v, c, q, η; reason: "always" in (iii) means for every η, so q₀ is uniform in η
--   - generalization: "η_L > 0 is uniquely defined by Π_L(η_L) = qΠ*" → 0 < η_L < 1, Π_L(η_L) = qP, and η_L is the only root of Π_L = qP on [0, 1); reason: [0, 1) is the domain of Π_L; η_L < 1 is additional content
--   - encoding: Π_L undefined at η = 1 → Lean's x/0 = 0 gives Π_L(1) = −qc, so banProfit at η = 1 is Π_H(1) = q(v − c); reason: this is the paper's ban profit at η = 1 (p. 38: "when η = 1, profits are q (v − c)")
--   - correction: (iv): M prefers to ban for µ close to zero, for every η ∈ [0, 1] → under 0 < η ∨ c < qv; reason: counterexample v = 2, c = 1, q = 1/4, η = 0 (η = 0 is in the model, p. 15): the ban profit is max{0, qv − c} = 0 < qΠ*(µ) for every µ > 0; the added disjunction is exactly ban profit > 0, the limit of qΠ*(µ) as µ → 0, so it is minimal
--   - correction: (iv): M prefers to allow for µ large, for every η ∈ [0, 1] → under η < 1; reason: counterexample η = 1: the ban profit is q(v − c) > qΠ*(µ) for every µ > 0 because Π*(µ) < v − c; the paper itself says on p. 15 that at η = 1 M always wants to ban
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, Proposition 3, p. 15 (statement continuing on p. 16); proof §8.4, p. 38; Π*(µ) from (6), p. 10

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_piL
import Definitions.Def_MarketplaceLeakage_Communication_piStarUniform
import Definitions.Def_MarketplaceLeakage_Communication_PrefersBan
import Definitions.Def_MarketplaceLeakage_Communication_PrefersAllow

namespace MarketplaceLeakage.Communication

/-- **Proposition 3: when the marketplace prefers to ban communication.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), Proposition 3, p. 15 (statement ending on p. 16): "The marketplace prefers to ban
communication for all η > Π∗/(v−c). If q > c/(v−Π∗), then the marketplace also prefers to ban
communication when η < ηL, where ηL > 0 is uniquely defined by ΠL (ηL) = qΠ∗. If q is close
enough to one, the marketplace always prefers to ban communication. Finally, if G (s) = s/µ
and s̄ = µ, then the marketplace will prefer to ban (allow) communication when µ is
sufficiently close to zero (sufficiently large)."

Standing assumptions: value `v` and marginal cost `c` with `v > c` (p. 5) and `c > 0`
("positive marginal costs", p. 6); prior `0 < q < 1` (p. 14); `0 ≤ η ≤ 1` (p. 14). The allow
profit is `qΠ*` and the ban profit is `max{Π_H(η), Π_L(η)}` (p. 15).

Clauses (i)–(iii) hold for every `P` with `0 < P < v − c` in the role of `Π*` ("Recall
0 < Π∗ < v − c", p. 16). Clause (iv) takes `Π* = Π*(µ)` of (6) (uniform `G`).

**Formalization Note.**
* (i)–(iii) quantify over every `0 < P < v − c`: `Π*` of (3) enters them only through
  `0 < Π* < v − c`, so this covers `Π*` for every admissible `G`.
* "Prefers" is strict on both sides (`PrefersBan`, `PrefersAllow`).
* (ii): `η_L ∈ (0, 1)`, `Π_L(η_L) = qP`, and `η_L` is the only root of `Π_L = qP` on
  `[0, 1)`, the domain of `Π_L` (undefined at `η = 1`).
* (iii): `q₀ < 1` is uniform in `η ∈ [0, 1]` ("always"); it may depend on `v, c, P`.
* (iv): `µ₀ > 0` and `µ₁` may depend on `v, c, q, η`.
* At `η = 1`, Lean's `x / 0 = 0` gives `banProfit = Π_H(1) = q(v − c)`, the paper's ban
  profit at `η = 1` (p. 38).
* **Corrections in (iv).** The ban part assumes `η > 0 ∨ qv > c`: at `η = 0` with
  `qv ≤ c` the ban profit is `max{0, qv − c} = 0 < qΠ*(µ)` for every `µ > 0` (e.g. `v = 2`,
  `c = 1`, `q = 1/4`). The allow part assumes `η < 1`: at `η = 1` the ban profit is
  `q(v − c) > qΠ*(µ)` for every `µ > 0`, as the paper says on p. 15 ("When η = 1 [...] M will
  always want to do so"). -/
theorem proposition_3_ban_communication {v c : ℝ} (hc : 0 < c) (hcv : c < v) :
    (∀ P : ℝ, 0 < P → P < v - c →
      -- (i)
      (∀ q η : ℝ, 0 < q → q < 1 → P / (v - c) < η → η ≤ 1 → PrefersBan q v c η P) ∧
      -- (ii)
      (∀ q : ℝ, 0 < q → q < 1 → c / (v - P) < q →
        ∃ ηL : ℝ, 0 < ηL ∧ ηL < 1 ∧ piL q v c ηL = q * P ∧
          (∀ η : ℝ, 0 ≤ η → η < 1 → piL q v c η = q * P → η = ηL) ∧
          ∀ η : ℝ, 0 ≤ η → η < ηL → PrefersBan q v c η P) ∧
      -- (iii)
      (∃ q₀ : ℝ, q₀ < 1 ∧ ∀ q : ℝ, q₀ < q → q < 1 →
        ∀ η : ℝ, 0 ≤ η → η ≤ 1 → PrefersBan q v c η P)) ∧
    -- (iv): uniform G, Π* = Π*(µ) of (6)
    (∀ q η : ℝ, 0 < q → q < 1 → 0 ≤ η → η ≤ 1 →
      ((0 < η ∨ c < q * v) →
        ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
          PrefersBan q v c η (piStarUniform v c μ)) ∧
      (η < 1 →
        ∃ μ₁ : ℝ, ∀ μ : ℝ, μ₁ < μ → PrefersAllow q v c η (piStarUniform v c μ))) := by sorry

end MarketplaceLeakage.Communication
