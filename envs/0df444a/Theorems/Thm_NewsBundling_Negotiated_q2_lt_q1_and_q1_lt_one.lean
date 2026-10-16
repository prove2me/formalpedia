-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_q2_lt_q1_and_q1_lt_one
-- name    : NewsBundling.Negotiated.q2_lt_q1_and_q1_lt_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:02.843512+00:00
-- url     : https://prove2.me/theorems/627a6a65-4415-4f5e-abc1-2c4626e21adb
-- title:
--   Proof of Lemma 5, p. 33 — q₂(c) < q₁(c) (for β < 1) and q₁(c) < 1
-- statement:
--   Assume $\tfrac13<\beta\le1$, $c>2\beta$ and $0<\Lambda<\tfrac12$, and let $q_1(c)=(1+\beta)/(2c)$ and $q_2(c)=(\beta(2-\Lambda)-\Lambda)/(2(1-\Lambda)c)$. Then
--
--   $$q_1(c)<1,\qquad\text{and, if }\beta<1,\qquad q_2(c)<q_1(c).$$
--
--   These inequalities place the equilibrium quality of Lemma 5 inside $[0,1]$ and order the two thresholds of Lemma 5.
--
--   **Formalization Note** The paper states $q_2(c)<q_1(c)$ "for all $c$". At $\beta=1$ the two coincide ($q_1=q_2=1/c$), so the strict inequality is stated under $\beta<1$.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), App. A, proof of Lemma 5, p. 33, last paragraph (and p. 32, first sentence)

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem q2_lt_q1_and_q1_lt_one (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    (β < 1 → q2 β c Λ < q1 β c) ∧ q1 β c < 1 := by sorry

end NewsBundling.Negotiated
