-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_eta_star
-- name    : MarketplaceLeakage.Communication.eta_star
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:21.689856+00:00
-- url     : https://prove2.me/theorems/50f00960-61d6-49af-a605-23e838ed9c3d
-- title:
--   §8.4, p. 38 — when qv > c a unique η* ∈ (0, 1) separates Π_H ≥ Π_L (η ≥ η*) from Π_H ≤ Π_L (η ≤ η*)
-- statement:
--   Let $0<v$, $c<v$, $0<q<1$ and $qv>c$, and put
--   $$\eta^*=\frac{qv(2-q)-c-q\sqrt{(1-q)\,v\,(v-c)}}{qv\,\bigl(3(1-q)+q^2\bigr)-c}.$$
--   Then $0<\eta^*<1$, and for every $\eta\in[0,1)$,
--   $$\Pi_L(\eta)\le\Pi_H(\eta)\iff \eta\ge\eta^* .$$
--   In particular $\Pi_H(\eta)\ge\Pi_L(\eta)$ for $\eta\ge\eta^*$ and $\Pi_H(\eta)\le\Pi_L(\eta)$ for $\eta\le\eta^*$, and $\eta^*$ is the unique such point.
--
--   So under a ban the marketplace induces the low price for little information ($\eta<\eta^*$) and the high price for much information; its ban profit is first decreasing and then increasing in $\eta$, with its minimum at $\eta^*$.
--
--   **Formalization Note.** $v>0$ is added, as in the derivative lemma: the proof relies on $\Pi_L$ being decreasing, which needs it. The equivalence is stated for $\eta<1$ because $\Pi_L$ divides by $1-\eta$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 38, §8.4, Proof of Proposition 3, display η*

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

namespace MarketplaceLeakage.Communication

theorem eta_star (v c : ℝ) (hvc : c < v) (hv : 0 < v) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hqv : c < q * v) :
    0 < etaStar v c q ∧ etaStar v c q < 1 ∧
      ∀ η : ℝ, 0 ≤ η → η < 1 → (PiL v c q η ≤ PiH v c q η ↔ etaStar v c q ≤ η) := by sorry

end MarketplaceLeakage.Communication
