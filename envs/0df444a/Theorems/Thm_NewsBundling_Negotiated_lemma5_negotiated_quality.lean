-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_lemma5_negotiated_quality
-- name    : NewsBundling.Negotiated.lemma5_negotiated_quality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:01.613058+00:00
-- url     : https://prove2.me/theorems/144b693a-fb6b-4cdf-9f9b-9c3afb562477
-- title:
--   Lemma 5, p. 20 — equilibrium quality under negotiated content bundling is q₂(c), Λ or q₁(c)
-- statement:
--   Assume $\tfrac13<\beta\le1$, $c>2\beta$ and $0<\Lambda<\tfrac12$. The negotiated content-bundling game has a subgame-perfect equilibrium, and in every such equilibrium the publisher's quality is
--
--   $$\tilde q=\begin{cases} q_2(c)=\dfrac{\beta(2-\Lambda)-\Lambda}{2(1-\Lambda)c}, & c<\dfrac{\beta(2-\Lambda)-\Lambda}{2(1-\Lambda)\Lambda},\\[3mm] \Lambda, & \dfrac{\beta(2-\Lambda)-\Lambda}{2(1-\Lambda)\Lambda}\le c\le\dfrac{1+\beta}{2\Lambda},\\[3mm] q_1(c)=\dfrac{1+\beta}{2c}, & c>\dfrac{1+\beta}{2\Lambda}.\end{cases}$$
--
--   When quality is cheap the publisher keeps some direct traffic ($q>\Lambda$); when it is costly the publisher's content is distributed through the platform only. This is the negotiated side of Proposition 5's comparison.
--
--   **Formalization Note** The existence conjunct rules out a vacuous "every equilibrium" statement.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 20, Lemma 5; App. A, proof of Lemma 5, pp. 32–33

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem lemma5_negotiated_quality (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    (∃ σ, IsNegotiatedSPE β c Λ σ) ∧
      ∀ σ, IsNegotiatedSPE β c Λ σ →
        σ.quality =
          if c < (β * (2 - Λ) - Λ) / (2 * (1 - Λ) * Λ) then q2 β c Λ
          else if c ≤ (1 + β) / (2 * Λ) then Λ
          else q1 β c := by sorry

end NewsBundling.Negotiated
