-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_etaStar_unique_crossing
-- name    : MarketplaceLeakage.Communication.etaStar_unique_crossing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:05:39.556677+00:00
-- url     : https://prove2.me/theorems/0010c9cf-e832-40a4-aaa1-055b60c232c5
-- title:
--   For $qv>c$ the ban options cross at the unique $\eta^*\in(0,1)$
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Let $0<c<v$, $0<q<1$ and $qv>c$, and let
--
--   $$
--   \eta^*=\frac{qv(2-q)-c-q\sqrt{(1-q)v(v-c)}}{qv(3(1-q)+q^2)-c}.
--   $$
--
--   Then $0<\eta^*<1$ and, for every $\eta\in[0,1)$:
--
--   1. if $\eta\ge\eta^*$ then $\Pi_H(\eta)\ge\Pi_L(\eta)$ (M prefers option 1);
--   2. if $\eta\le\eta^*$ then $\Pi_H(\eta)\le\Pi_L(\eta)$ (M prefers option 2);
--   3. $\Pi_H(\eta)=\Pi_L(\eta)$ only at $\eta=\eta^*$.
--
--   So the marketplace's ban profit is decreasing and then increasing in $\eta$, with its minimum at $\eta^*$.
--
--   Differences from the source:
--
--   - encoding: the comparison for η in the model's [0, 1] → for η ∈ [0, 1); reason: Π_L is undefined at η = 1
--   - reading: "there exists a unique η* ∈ (0, 1) such that ..." → the explicit η* lies in (0, 1), has the sign pattern, and is the only crossing point of Π_H and Π_L on [0, 1); reason: any point with the sign pattern is a crossing point, so this gives the page's uniqueness
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §8.4 (proof of Proposition 3), unnumbered display, p. 38

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_piH
import Definitions.Def_MarketplaceLeakage_Communication_piL
import Definitions.Def_MarketplaceLeakage_Communication_etaStar

namespace MarketplaceLeakage.Communication

/-- **For `qv > c` the two ban options cross at the unique `η* ∈ (0, 1)`.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §8.4 (proof of Proposition 3), unnumbered display, p. 38: "Thus, when qv > c, there exists
a unique η∗ ∈ (0, 1) such that M prefers option 1 (ΠH (η) ≥ ΠL (η)) when η ≥ η∗ and option 2
(ΠH (η) ≤ ΠL (η)) when η ≤ η∗, where
η∗ = (qv (2 − q) − c − q √((1 − q) v (v − c)))/(qv (3 (1 − q) + q²) − c)."

Standing assumptions `0 < c < v` (pp. 5–6), `0 < q < 1` (p. 14), and `qv > c`. Then
`0 < η* < 1`, and for every `η ∈ [0, 1)`: `Π_H(η) ≥ Π_L(η)` if `η ≥ η*`,
`Π_H(η) ≤ Π_L(η)` if `η ≤ η*`, and `Π_H(η) = Π_L(η)` only at `η = η*`.

**Formalization Note.** `Π_L` is undefined at `η = 1`, so the comparison ranges over
`[0, 1)`. The uniqueness is stated as uniqueness of the crossing point, which implies the
uniqueness of a `η*` with the stated sign pattern (such a point is a crossing point). -/
theorem etaStar_unique_crossing {q v c : ℝ} (hc : 0 < c) (hcv : c < v) (hq0 : 0 < q)
    (hq1 : q < 1) (hqv : c < q * v) :
    0 < etaStar q v c ∧ etaStar q v c < 1 ∧
      ∀ η : ℝ, 0 ≤ η → η < 1 →
        (etaStar q v c ≤ η → piL q v c η ≤ piH q v c η) ∧
        (η ≤ etaStar q v c → piH q v c η ≤ piL q v c η) ∧
        (piH q v c η = piL q v c η → η = etaStar q v c) := by sorry

end MarketplaceLeakage.Communication
