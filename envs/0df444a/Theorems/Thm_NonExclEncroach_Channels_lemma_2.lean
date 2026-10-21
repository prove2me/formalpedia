-- Prove2me | Theorems.Thm_NonExclEncroach_Channels_lemma_2
-- name    : NonExclEncroach.Channels.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:29.222039+00:00
-- url     : https://prove2.me/theorems/9fba3ee1-9e04-4a62-8a6a-7ba4cf6e8051
-- title:
--   Lemma 2, p. 16 — the reseller's conditionally optimal order from supplier 2, q2^III(w2, w′2, q1)
-- statement:
--   Fix $\theta\in(0,1)$ and $c$ with $c_0(\theta)<c<c_3(\theta)$, supplier 2's actual price $w_2\ge0$, supplier 1's belief $w_2'\ge0$, any $w_1$, and an order $q_1\ge0$ from supplier 1. Suppose supplier 1 sells $y=y^{III}(w_2',q_1)$ directly (Lemma 1). Then the reseller's profit, as a function of the order $q_2\ge0$ from supplier 2, has exactly one maximizer, namely
--   $$q_2^{III}(w_2,w_2',q_1)=\begin{cases}\dfrac{2(1-w_2)-\theta(1-c)-3\theta q_1}{4-\theta^2}-\dfrac{\theta^2(w_2'-w_2)}{2(4-\theta^2)}, & q_1\le\bar q_1(w_2'),\\[4pt] \left[\tfrac12(1-2\theta q_1-w_2)\right]^+, & q_1>\bar q_1(w_2'),\end{cases}$$
--   provided the upper branch is non-negative whenever $q_1\le\bar q_1(w_2')$.
--
--   Because the reseller knows both $w_2$ and $w_2'$, his order from supplier 2 reacts to the true price while supplier 1's direct sales react to her belief; this lemma is what drives supplier 2's incentive to deviate from the price supplier 1 expects.
--
--   **Formalization Note** The page writes the upper branch without a positive part. Where it would be negative the maximizer is $0$, so the statement assumes it is non-negative when $q_1\le\bar q_1(w_2')$; this is a disclosed, necessary addition.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, p. 16 (PDF 16), Lemma 2, (4.19); proof: Online Technical Appendix p. 5 (PDF 38)

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

namespace NonExclEncroach.Channels

theorem lemma_2 (θ c w1 w2 b q1 : ℝ) (hS : Standing θ c) (hw2 : 0 ≤ w2) (hb : 0 ≤ b)
    (hq1 : 0 ≤ q1) (hpos : q1 ≤ qbar1 θ c b → 0 ≤ q2IIIUpper θ c w2 b q1) :
    IsBestResponse (fun z => resellerProfit θ q1 z w1 w2 (yIII θ c b q1)) (q2III θ c w2 b q1) ∧
      ∀ z, IsBestResponse (fun z => resellerProfit θ q1 z w1 w2 (yIII θ c b q1)) z →
        z = q2III θ c w2 b q1 := by sorry

end NonExclEncroach.Channels
