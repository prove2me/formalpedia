-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_endpoint_values_and_limits
-- name    : MarketplaceLeakage.Communication.endpoint_values_and_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:04:41.017418+00:00
-- url     : https://prove2.me/theorems/6355b84a-54d0-463b-aa4b-a66140a1ca61
-- title:
--   $\Pi_H(0)=0<\Pi_L(0)=qv-c$; $\lim\Pi_H>0>\lim\Pi_L=-\infty$ as $\eta\to1$
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Let $0<c<v$, $0<q<1$ and $qv>c$. Then
--
--   $$
--   \Pi_H(0)=0<\Pi_L(0)=qv-c,
--   $$
--
--   and, as $\eta\to1^-$,
--
--   $$
--   \Pi_H(\eta)\to q(v-c)>0,\qquad \Pi_L(\eta)\to-\infty .
--   $$
--
--   So for $qv>c$ the low-price option is better near $\eta=0$ and the high-price option near $\eta=1$.
--
--   Differences from the source:
--
--   - encoding: lim_{η→1} → the left limit η → 1⁻; reason: η ≤ 1 in the model and Π_L is undefined at η = 1
--   - generalization: lim_{η→1} Π_H(η) > 0 → Π_H(η) → q(v − c) and q(v − c) > 0; reason: the value of the limit is stated as well; it implies the page's claim
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §8.4 (proof of Proposition 3), unnumbered displays, p. 38

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_piH
import Definitions.Def_MarketplaceLeakage_Communication_piL

namespace MarketplaceLeakage.Communication

open Filter Topology

/-- **Endpoint values and limits of `Π_H` and `Π_L` when `qv > c`.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §8.4 (proof of Proposition 3), unnumbered displays, p. 38: "Suppose now qv > c. We have
ΠH (0) = 0 < ΠL (0) = qv − c. and lim_{η→1} ΠH (η) > 0 > lim_{η→1} ΠL (η) = −∞."

Standing assumptions `0 < c < v` (pp. 5–6), `0 < q < 1` (p. 14), and `qv > c`. Then
`Π_H(0) = 0`, `Π_L(0) = qv − c > 0`, `Π_H(η) → q(v − c) > 0` and `Π_L(η) → −∞` as
`η → 1⁻`.

**Formalization Note.** `η ≤ 1` in the model, so `lim_{η→1}` is the left limit
(`𝓝[<] 1`). The value `q(v − c)` of the limit of `Π_H` is stated explicitly together with
its positivity. -/
theorem endpoint_values_and_limits {q v c : ℝ} (hc : 0 < c) (hcv : c < v) (hq0 : 0 < q)
    (hq1 : q < 1) (hqv : c < q * v) :
    piH q v c 0 = 0 ∧ piL q v c 0 = q * v - c ∧ 0 < q * v - c ∧
      Tendsto (piH q v c) (𝓝[<] 1) (𝓝 (q * (v - c))) ∧ 0 < q * (v - c) ∧
      Tendsto (piL q v c) (𝓝[<] 1) atBot := by sorry

end MarketplaceLeakage.Communication
