-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_eq6_fee_high
-- name    : NewsBundling.Negotiated.eq6_fee_high
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:00.641846+00:00
-- url     : https://prove2.me/theorems/c52a68f6-79b2-474c-95ef-e838fdd330c6
-- title:
--   (6), p. 20 — for q > Λ the negotiated fee is F₂(q) = (1 − q)(1 + β)Λ/(2(1 − Λ))
-- statement:
--   Assume $\tfrac13<\beta\le1$, $c>2\beta$ and $0<\Lambda<\tfrac12$. In every subgame-perfect equilibrium of the negotiated content-bundling game, the lump-sum payment agreed at a quality $q\in(\Lambda,1]$ is
--
--   $$F(q)=\frac{(1-q)(1+\beta)\Lambda}{2(1-\Lambda)}\equiv F_2(q).$$
--
--   For such $q$ the platform shows $\lambda=\Lambda$, the publisher keeps direct traffic $T_1=(q-\Lambda)/(1-\Lambda)$, and the fee is the unique maximizer of the Nash product of display (5),
--
--   $$\Bigl(\beta\frac{q-\Lambda}{1-\Lambda}+F-\beta q\Bigr)\Bigl(\frac{1-q}{1-\Lambda}-F-(1-q)\Bigr).$$
--
--   This is the high-quality branch of the publisher's stage-1 profit (7).
--
--   **Formalization Note** At $q=1$ the consumer spends all her time on the publisher's site whatever $\lambda$ is, and both sides equal $0$.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 20, §6, displays (5) and (6)

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem eq6_fee_high (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    ∀ σ, IsNegotiatedSPE β c Λ σ → ∀ q ∈ Set.Ioc Λ 1,
      σ.fee q = (1 - q) * (1 + β) * Λ / (2 * (1 - Λ)) := by sorry

end NewsBundling.Negotiated
