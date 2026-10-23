-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_eq4_fee_low
-- name    : NewsBundling.Negotiated.eq4_fee_low
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:53.834721+00:00
-- url     : https://prove2.me/theorems/4c0dfbf8-0306-4d34-9c76-cd03c6aa3e3c
-- title:
--   (4), p. 19 — for q ≤ Λ the negotiated fee is F₁(q) = q(1 + β)/2
-- statement:
--   Assume $\tfrac13<\beta\le1$, $c>2\beta$ and $0<\Lambda<\tfrac12$. In every subgame-perfect equilibrium of the negotiated content-bundling game, the lump-sum payment agreed at a quality $q\in[0,\Lambda]$ is
--
--   $$F(q)=\frac{q(1+\beta)}{2}\equiv F_1(q).$$
--
--   For such $q$ the platform shows $\lambda=q$, all news consumption happens on the platform, and the fee is the unique maximizer of the Nash product $(F-\beta q)(1-F-(1-q))$ of display (3). This is the low-quality branch of the publisher's stage-1 profit (7).
--
--   **Formalization Note** The page states (3)–(4) for $q<\Lambda$; the statement includes $q=\Lambda$, where the platform also chooses $\lambda=q$ and (4) and (6) coincide. The fee is a component of the equilibrium profile that maximizes the Nash product over all real $F$; it is not defined by the formula.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 19, §6, displays (3) and (4)

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem eq4_fee_low (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    ∀ σ, IsNegotiatedSPE β c Λ σ → ∀ q ∈ Set.Icc (0 : ℝ) Λ, σ.fee q = q * (1 + β) / 2 := by sorry

end NewsBundling.Negotiated
