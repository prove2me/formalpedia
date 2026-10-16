-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_prop5_preamble
-- name    : NewsBundling.Negotiated.prop5_preamble
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:02.575315+00:00
-- url     : https://prove2.me/theorems/9cbe30d8-f25c-47b8-94a8-9fbfe2d8eeba
-- title:
--   Proof of Proposition 5, p. 33 — for β < 1, q₂(c) < q̂(c) = β/c < q₁(c)
-- statement:
--   Assume $\tfrac13<\beta\le1$, $c>2\beta$ and $0<\Lambda<\tfrac12$. If $\beta<1$, then
--
--   $$q_2(c)=\frac{\beta(2-\Lambda)-\Lambda}{2(1-\Lambda)c}<\hat q(c)=\frac{\beta}{c}<q_1(c)=\frac{1+\beta}{2c}.$$
--
--   The benchmark quality therefore lies strictly between the two interior qualities of Lemma 5.
--
--   **Formalization Note** At $\beta=1$ all three quantities equal $1/c$, so the page's strict inequalities need $\beta<1$, which is added as a hypothesis.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), App. A, proof of Proposition 5, p. 33, first sentence

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem prop5_preamble (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    β < 1 → q2 β c Λ < β / c ∧ β / c < q1 β c := by sorry

end NewsBundling.Negotiated
