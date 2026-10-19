-- Prove2me | Theorems.Thm_NonExclEncroach_Channels_proposition_5
-- name    : NonExclEncroach.Channels.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:49.131385+00:00
-- url     : https://prove2.me/theorems/25b9a746-eb1c-499c-9b01-482c2f440fbe
-- title:
--   Proposition 5, p. 22 — θ̂12 ∈ (0,1): below it supplier 1 sells only directly at some c > 0; above it, through both channels at some c < 0
-- statement:
--   There is a threshold $\hat\theta_{12}\in(0,1)$, the root of $\mathrm{Num1}$, such that:
--
--   1. for every $\theta_{12}\in(0,\hat\theta_{12})$ we have $c_2>0$, and for every direct cost $c\in(0,c_2]$ the game has an equilibrium and in every equilibrium supplier 1 sells only through her direct channel ($q_1^*=0<y^*$), even though her direct channel is less efficient than the reselling channel;
--   2. for every $\theta_{12}\in(\hat\theta_{12},1)$ we have $c_2<0$; and for every $\theta_{12}\in(\hat\theta_{12},9/10]$ and every direct cost $c\in(c_2,0)$ there is an equilibrium in which supplier 1 sells through both channels ($q_1^*>0$ and $y^*>0$), even though her direct channel is more efficient than the reselling channel.
--
--   In symbols, with $\mathcal E(\theta,c)$ the set of equilibria,
--   $$\exists\,\hat\theta\in(0,1),\ \mathrm{Num1}(\hat\theta)=0:\quad \begin{cases}\theta<\hat\theta,\ 0<c\le c_2(\theta)\ \Rightarrow\ \mathcal E\ne\emptyset\ \text{and}\ q_1^*=0<y^*\ \text{on}\ \mathcal E,\\ \hat\theta<\theta\le 9/10,\ c_2(\theta)<c<0\ \Rightarrow\ \exists\,\sigma\in\mathcal E:\ q_1^*>0,\ y^*>0.\end{cases}$$
--
--   With an exclusive reseller ($\theta_{12}=0$) neither happens: the encroaching supplier always uses the reseller when $c>0$ and never when $c\le0$. Non-exclusivity reverses both conclusions, depending on how substitutable the two suppliers' products are.
--
--   **Formalization Note** The threshold is pinned as the root of $\mathrm{Num1}$, as in the paper's proof. The paper's "there exist positive (negative) values of $c$" is strengthened to every $c\in(0,c_2]$ (every $c\in(c_2,0)$), which is what Lemma 4 gives; part (a) also asserts that every equilibrium has $q_1^*=0$, as the paper's proof of Lemma 4 claims uniqueness for $c\le c_2$. Part (b) asserts existence only, as in the paper, and is stated for $\theta_{12}\le 9/10$: a numerical solution of the game finds that for $\theta_{12}\ge0.96$ the $R\&D$ prices of Table 1 are not an equilibrium at some negative $c$ (for $\theta_{12}\ge0.98$ at every tested $c\in(c_2,0)$), because the reseller then prefers an order outside the region the paper's Lemmas 1–3 restrict to; whether some other equilibrium with $q_1^*>0$ exists there is open. The standing range $c_0<c<c_3$ holds automatically for the costs in both parts.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, p. 22 (PDF 22), Proposition 5; proof: Online Technical Appendix p. 16 (PDF 49)

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

namespace NonExclEncroach.Channels

theorem proposition_5 :
    ∃ θhat : ℝ, 0 < θhat ∧ θhat < 1 ∧ num1 θhat = 0 ∧
      (∀ θ, 0 < θ → θ < θhat →
        0 < c2 θ ∧
        ∀ c, 0 < c → c ≤ c2 θ →
          (∃ σ, IsEquilibrium θ c σ) ∧
          ∀ σ, IsEquilibrium θ c σ → σ.q1 = 0 ∧ 0 < σ.y) ∧
      (∀ θ, θhat < θ → θ < 1 → c2 θ < 0) ∧
      (∀ θ, θhat < θ → θ ≤ 9 / 10 →
        ∀ c, c2 θ < c → c < 0 →
          ∃ σ, IsEquilibrium θ c σ ∧ 0 < σ.q1 ∧ 0 < σ.y) := by sorry

end NonExclEncroach.Channels
