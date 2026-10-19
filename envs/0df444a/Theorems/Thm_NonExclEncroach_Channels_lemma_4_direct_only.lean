-- Prove2me | Theorems.Thm_NonExclEncroach_Channels_lemma_4_direct_only
-- name    : NonExclEncroach.Channels.lemma_4_direct_only
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:29.774034+00:00
-- url     : https://prove2.me/theorems/3cbf5288-168d-45d9-afe4-3b3e69ec9420
-- title:
--   Lemma 4 (DO and DOB columns of Table 1), p. 18 — for c ≤ c2 the Table 1 prices are equilibria and every equilibrium sells only directly; stated for θ12 ≤ 9/10
-- statement:
--   Let $0<\theta\le 9/10$ and $c_0(\theta)<c\le c_2(\theta)$. Write
--   $$\bar w(w_2,w_2')=\frac{(1-\theta)(8-\theta^3+8(1+\theta)c)+3\theta(4-\theta^2)w_2-4\theta(1-\theta^2)w_2'}{(4-\theta^2)^2}$$
--   for the price at or above which the reseller orders nothing from supplier 1. Then:
--   1. **Direct Only** ($c\le c_1$): for every price $w_1\ge 0$ with $w_1\ge\bar w(w_2^{DO},w_2^{DO})$ there is an equilibrium with wholesale prices $(w_1,\,w_2^{DO})$, where $w_2^{DO}=\dfrac{2(2-\theta(1-c))}{8-\theta^2}$;
--   2. **Direct Only Boundary** ($c\ge c_1$): there is an equilibrium with wholesale prices $w_1^{DOB}=\dfrac{4(1-\theta^2)(2+\theta^2-6c)}{(4-\theta^2)(4+5\theta^2)}$ and $w_2^{DOB}=\dfrac{(1-\theta)(4\theta-4\theta^2+\theta^3-16c(1+\theta))}{\theta(4+5\theta^2)}$;
--   3. every equilibrium has $q_1^*=0$ and $y^*>0$: supplier 1 sells only through her direct channel.
--
--   This is the part of Lemma 4 behind Proposition 5(a): when the direct cost is at most $c_2$, the encroaching supplier does not use the reseller at all.
--
--   **Formalization Note** Lemma 4 is stated in the paper for all $\theta\in(0,1)$. A numerical solution of the game (exact stage III, the reseller's exact optimum, grid best responses of both suppliers) finds that at $\theta=0.97$ and $\theta=0.99$ with $c=-0.3$ the Direct Only Boundary prices are not an equilibrium: the reseller then prefers a large $q_1$ that drives supplier 1's conjecture $q_2'$ to $0$, a region the paper's Lemmas 1–3 exclude by restriction. The statement is therefore made for $\theta\le 9/10$, where the numerical check confirms the table. The paper's "$[\bar w,\infty]$" for $w_1^*$ in the DO column is read as the set of supplier 1's equilibrium prices $w_1\ge\bar w(w_2^{DO},w_2^{DO})$. The paper's proof (Online Technical Appendix p. 10) announces uniqueness of the equilibrium prices for $c\le c_2$, but it only shows that the Table 1 prices admit no profitable deviation. Uniqueness of the prices is false: at $\theta=0.6$, $c=-0.2$ (so $c<c_1$), the profile with $w_2=w_2^{DO}-0.05\approx0.2851$ and $w_1=\bar w(w_2,w_2)\approx0.2656$ is also an equilibrium. A small rise in $w_2$ there makes the reseller order from supplier 1, so supplier 2's profit has a kink at $w_2$ and is maximal there. The same happens in the DOB regime. The Table 1 prices are therefore stated as existence, and "every equilibrium" is kept only for $q_1^*=0<y^*$, which holds at these other equilibria too.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, p. 18 (PDF 18), Lemma 4 and Table 1 (DO and DOB columns); proof: Online Technical Appendix pp. 10–14 (PDF 43–47)

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

namespace NonExclEncroach.Channels

theorem lemma_4_direct_only (θ c : ℝ) (hS : Standing θ c) (hθ : θ ≤ 9 / 10) (hc : c ≤ c2 θ) :
    (c ≤ c1 θ → ∀ w1, 0 ≤ w1 → wU θ c (wDO2 θ c) (wDO2 θ c) ≤ w1 →
      ∃ σ, IsEquilibrium θ c σ ∧ σ.w1 = w1 ∧ σ.w2 = wDO2 θ c) ∧
    (c1 θ ≤ c → ∃ σ, IsEquilibrium θ c σ ∧ σ.w1 = wDOB1 θ c ∧ σ.w2 = wDOB2 θ c) ∧
    ∀ σ, IsEquilibrium θ c σ → σ.q1 = 0 ∧ 0 < σ.y := by sorry

end NonExclEncroach.Channels
