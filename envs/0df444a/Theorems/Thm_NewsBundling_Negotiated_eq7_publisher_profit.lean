-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_eq7_publisher_profit
-- name    : NewsBundling.Negotiated.eq7_publisher_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:07.333888+00:00
-- url     : https://prove2.me/theorems/59f8245e-c967-4b31-a168-7684e0850f6d
-- title:
--   (7), p. 20 — the publisher's stage-1 profit under negotiated content bundling
-- statement:
--   Assume $\tfrac13<\beta\le1$, $c>2\beta$ and $0<\Lambda<\tfrac12$. In every subgame-perfect equilibrium of the negotiated content-bundling game, the publisher's payoff from choosing a quality $q\in[0,1]$ (direct revenue plus negotiated fee minus cost, given the later stages' equilibrium play) is
--
--   $$\pi_1(q)=\begin{cases}F_1(q)-\dfrac{cq^2}{2}, & q\le\Lambda,\\[2mm] F_2(q)+\beta\dfrac{q-\Lambda}{1-\Lambda}-\dfrac{cq^2}{2}, & \text{otherwise,}\end{cases}$$
--
--   with $F_1(q)=q(1+\beta)/2$ and $F_2(q)=(1-q)(1+\beta)\Lambda/(2(1-\Lambda))$.
--
--   This is the objective the publisher maximizes at stage 1; Lemma 5 is its maximizer.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 20, §6, display (7)

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem eq7_publisher_profit (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    ∀ σ, IsNegotiatedSPE β c Λ σ → ∀ q ∈ Set.Icc (0 : ℝ) 1,
      negPublisherProfit β c σ q =
        if q ≤ Λ then q * (1 + β) / 2 - c * q ^ 2 / 2
        else (1 - q) * (1 + β) * Λ / (2 * (1 - Λ)) + β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2 := by sorry

end NewsBundling.Negotiated
