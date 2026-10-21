-- Prove2me | Theorems.Thm_NonExclEncroach_Channels_lemma_1
-- name    : NonExclEncroach.Channels.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:29.941577+00:00
-- url     : https://prove2.me/theorems/abe07a6d-1769-4264-a361-7a2648b38b42
-- title:
--   Lemma 1, p. 15 — supplier 1's direct quantity y^III(w′2, q1) and her conjecture q′2(w′2, q1), threshold q̄1(w′2)
-- statement:
--   Fix the substitutability $\theta\in(0,1)$ and a direct cost $c$ with $c_0(\theta)<c<c_3(\theta)$. Let $w_2'\ge0$ be supplier 1's belief about supplier 2's wholesale price and let $q_1\ge0$ be the reseller's observed order from supplier 1. Set
--   $$\bar q_1(w_2')=\frac{2(1-c)-\theta(1-w_2')}{2(1-\theta^2)} .$$
--   Assume $w_2'$ satisfies the restriction of the lemma: the upper branch of $q_2'$ below is positive for every $x\in[0,\bar q_1(w_2')]$.
--
--   Then the stage-III problem (supplier 1's direct quantity $y$ and her conjecture $q_2'$ being mutual best responses under the belief $w_2'$) has exactly one solution, namely
--   $$y^{III}(w_2',q_1)=\begin{cases}\dfrac{2(1-c)-\theta(1-w_2')}{4-\theta^2}-\dfrac{2(1-\theta^2)}{4-\theta^2}\,q_1, & q_1\le\bar q_1(w_2'),\\[4pt] 0, & \text{otherwise},\end{cases}$$
--   $$q_2'(w_2',q_1)=\begin{cases}\dfrac{2(1-w_2')-\theta(1-c)}{4-\theta^2}-\dfrac{3\theta}{4-\theta^2}\,q_1, & q_1\le\bar q_1(w_2'),\\[4pt] \left[\tfrac12(1-2\theta q_1-w_2')\right]^+, & q_1>\bar q_1(w_2').\end{cases}$$
--
--   The lemma is the building block of the whole analysis: it gives supplier 1's reaction to any order the reseller places, which the reseller anticipates in stage II.
--
--   **Formalization Note** The restriction "for any $w_2'$ for which $q_2'(w_2',q_1)>0$ when $q_1\le\bar q_1(w_2')$" is the hypothesis on the upper branch of (4.18) over $[0,\bar q_1(w_2')]$. The statement asserts both that the displayed pair solves stage III and that it is the only solution.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, p. 15 (PDF 15), Lemma 1, (4.17)–(4.18)

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

namespace NonExclEncroach.Channels

theorem lemma_1 (θ c b q1 : ℝ) (hS : Standing θ c) (hb : 0 ≤ b) (hq1 : 0 ≤ q1)
    (hR : ∀ x, 0 ≤ x → x ≤ qbar1 θ c b → 0 < q2conjUpper θ c b x) :
    IsStageIII θ c b q1 (yIII θ c b q1) (q2conj θ c b q1) ∧
      ∀ y q2', IsStageIII θ c b q1 y q2' → y = yIII θ c b q1 ∧ q2' = q2conj θ c b q1 := by sorry

end NonExclEncroach.Channels
