-- Prove2me | Theorems.Thm_NonExclEncroach_Channels_lemma_4_reseller_and_direct
-- name    : NonExclEncroach.Channels.lemma_4_reseller_and_direct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:31.194704+00:00
-- url     : https://prove2.me/theorems/74db2497-0d74-4412-9ab6-6dc3de7a04b4
-- title:
--   Lemma 4 (R&D column of Table 1), Online Technical Appendix p. 10 — for c2 < c < 0 the R&D prices are an equilibrium with q1* > 0, y* > 0 (stated for θ12 ≤ 9/10)
-- statement:
--   Let $0<\theta\le 9/10$ and $c_2(\theta)<c<0$ (so $c_0<c<c_3$ as well). Then there is an equilibrium in which the wholesale prices are
--   $$w_1^*=w_1^{R\&D}=\frac{128(3-c)-\theta\Big(128+\theta\big(56+\theta(96+\theta(90-5\theta^4+\theta^3+34\theta^2c+18\theta+6c))-168c\big)\Big)}{3(256+2\theta^8-11\theta^6-52\theta^4+48\theta^2)},$$
--   $$w_2^*=w_2^{R\&D}=\frac{(1-\theta)(8+\theta^2)\big(16+\theta(8-3\theta^3-4(1+\theta)(2-\theta^2)c+4\theta)\big)}{256+2\theta^8-11\theta^6-52\theta^4+48\theta^2},$$
--   and supplier 1 sells through both channels: $q_1^*>0$ and $y^*>0$.
--
--   This is the part of Lemma 4 behind Proposition 5(b): when the direct cost exceeds $c_2$, supplier 1 also sells through the reseller.
--
--   **Formalization Note** The paper states this for all $c\in[c_2,c_3]$ and all $\theta$. The statement takes $c>c_2$ strictly, because at $c=c_2$ the reseller's order from supplier 1 is $0$. A numerical solution of the game finds that the $R\&D$ prices are not an equilibrium for some $\theta\ge0.85$ with $c>0.3$ (for instance $\theta=0.85$, $c=0.42$: supplier 1 gains by cutting $w_1$ to about $0.098$, after which the reseller orders $q_1\approx0.58$ and nothing from supplier 2), and for $\theta\ge0.96$ with negative $c$. The paper's Lemmas 1–3 exclude by restriction the region where this happens. The $R\&D$ prices also fail just below $c_3$ for $c>0$, for $\theta$ at least between $0.3$ and $0.8$: for instance at $\theta=1/2$, $c=c_3-0.002$ supplier 2 gains by raising $w_2$ from about $0.28$ to about $0.33$. The reseller then orders exactly $\bar q_1(w_2')$ from supplier 1, which shuts down the direct channel. The paper's first-order condition (4.23) is local and does not see this deviation. The statement is therefore made on the region the goal needs, $c_2<c<0$ with $\theta\le 9/10$, where the numerical check confirms the table. It asserts existence only, as the paper's proof does.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, p. 18 (PDF 18), Lemma 4 and Table 1 (R&D column); Online Technical Appendix p. 10 (PDF 43); Table 2, p. 33 (PDF 33)

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

namespace NonExclEncroach.Channels

theorem lemma_4_reseller_and_direct (θ c : ℝ) (hS : Standing θ c) (hc : c2 θ < c)
    (hθ : θ ≤ 9 / 10) (hc0 : c < 0) :
    ∃ σ, IsEquilibrium θ c σ ∧ σ.w1 = wRD1 θ c ∧ σ.w2 = wRD2 θ c ∧ 0 < σ.q1 ∧ 0 < σ.y := by sorry

end NonExclEncroach.Channels
