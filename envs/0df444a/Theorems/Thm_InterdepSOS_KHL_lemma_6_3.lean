-- Prove2me | Theorems.Thm_InterdepSOS_KHL_lemma_6_3
-- name    : InterdepSOS.KHL.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:39.520979+00:00
-- url     : https://prove2.me/theorems/edb68132-4e5a-4705-9772-6d982d3cb356
-- title:
--   Lemma 6.3, p. 21 — Random Sampling gives a 4-approximation to the OTHER component
-- statement:
--   Let $v$ be SOS valuations satisfying the standing assumptions on the grid $\{0,\dots,k-1\}^n$, let the Random Sampling allocations $\tilde T^{B}$ be produced by a maximizing selector as in the definition of the mechanism, let $\mathbf s$ be a grid profile and $T$ a feasible allocation. Then
--   $$\mathsf{OTHER}(T,\mathbf s)=\sum_i v_{iT_i}(\mathbf s_{-i},0_i)\;\le\;4\cdot\frac1{2^n}\sum_{B\subseteq[n]}\sum_i v_{i\tilde T^{B}_i}(\mathbf s),$$
--   the right-hand side being four times the expected welfare of Random Sampling, measured with the true values at the truthful profile, when the partition $(A,B)$ is uniform.
--
--   This is the half of the welfare decomposition (7) that Random Sampling covers; together with Lemma 6.2 it yields the ratio $k+3$ of Theorem 6.1.
--
--   **Formalization Note** The paper states the lemma for the OTHER component of a welfare-maximizing allocation; it is stated here for every feasible allocation $T$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 21, Lemma 6.3

import Mathlib
import Definitions.Def_InterdepSOS_KHL_Setting
import Definitions.Def_InterdepSOS_KHL_Mechanisms

namespace InterdepSOS.KHL
theorem lemma_6_3 {n m : ℕ} (k : ℕ) (v : Valuation n m)
    (hv : IsCombValuation k v) (hsos : ∀ i T, IsSOS k (v i T))
    (rsSel : Finset (Fin n) → Signal n → Allocation n m) (hrs : IsRSSelector k v rsSel)
    (s : Signal n) (hs : InGrid k s) (T : Allocation n m) (hT : IsAllocOn Finset.univ T) :
    other v T s ≤ 4 * rsAvg v rsSel s := by sorry
end InterdepSOS.KHL
