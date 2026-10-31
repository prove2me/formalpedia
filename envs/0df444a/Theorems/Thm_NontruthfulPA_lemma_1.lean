-- Prove2me | Theorems.Thm_NontruthfulPA_lemma_1
-- name    : NontruthfulPA.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:33.562654+00:00
-- url     : https://prove2.me/theorems/e44fac27-77d3-4a94-8ff7-dfd2a7a75eac
-- title:
--   Lemma 1 — an efficient $\alpha$-VCG equilibrium can be chosen envy-free
-- statement:
--   There are $k$ positions and $n \ge k$ bidders. The position vectors $\alpha, \beta \in \mathbb R^k_\ge$ are positive and non-increasing, with $\alpha_j = \beta_j = 0$ for $j > k$; bidder $i$ values position $j$ at $\beta_j v_i$ with $v_i \ge 0$. Bids are $b \in [0,\infty)^n$, and $b_{(t)}$ denotes the $t$-th highest bid, with $b_{(t)} = 0$ for $t > n$.
--
--   Let $\alpha, \beta \in \mathbb R^k_\ge$ and let $v_1 \ge \dots \ge v_n \ge 0$. If the $\alpha$-VCG mechanism possesses an efficient equilibrium, then it possesses an efficient equilibrium that is envy-free (22).
--
--   Envy-freeness is stronger than equilibrium, but by this lemma it comes for free in the $\alpha$-VCG mechanism. It is the first step of the proof of Theorem 1.
--
--   **Formalization Note** Bidders are `Fin n` and positions are 0-based ranks (rank $r$ is position $r+1$); $\alpha, \beta$ are functions on $\mathbb N$ that vanish from index $k$ on; the bids in rank order are padded by $0$ past rank $n$. Equilibria come with a ranking of the bidders, existentially quantified on both sides; equilibrium is the position-deviation equilibrium, efficiency means the ranking also orders the values, and envy-freeness uses the $\alpha$-VCG payments.
--
--   Differences from the source:
--   - generalization: v ∈ ℝ^n_≥ (positive and non-increasing) → v non-negative and non-increasing; reason: the proof never uses positivity; positive vectors are an instance
--   - reading: (Nash) equilibrium: p.6 allows every real deviation x under a fixed tie-breaking allocation; §3.1 (p.8) and §3.2 (p.11) describe it as a bidder raising or lowering its bid and being assigned a different position → IsPDEquilibrium: for every bidder i and every position r, moving i to r (others keep their order) at the price the mechanism charges on the deviated rank list does not raise i's utility; ties are resolved by the ranking σ; reason: §3's own notion; the mission uses it throughout because the main theorem is false under the p.6 notion (see Theorem 1)
--   - reading: efficient: b_i > b_j whenever v_i > v_j (p.6) → the ranking σ that orders the bids also orders the values; reason: the efficient assignment of p.6 (positions in order of valuations), read through the ranking; part of the position-deviation notion
--   - reading: bid profiles b ∈ ℝ^n (p.6) → bids b_i ≥ 0; reason: mechanisms charge non-negative payments (p.6) and §3.1 uses b_3 ≥ 0 (p.8); with negative bids the payments could be negative
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, Lemma 1, p.12

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- **Lemma 1**, Dütting–Fischer–Parkes, *Non-Truthful Position Auctions Are More Robust to
Misspecification*, arXiv:1602.07593v4, p.12: "Let α, β ∈ ℝ^k_≥ and v ∈ ℝ^n_≥, and assume that
the α-VCG mechanism possesses an efficient equilibrium. Then the α-VCG mechanism possesses an
efficient equilibrium that is envy-free."

**Formalization Note.** `v ∈ ℝ^n_≥` (positive, non-increasing, p.6) is relaxed to non-negative
and non-increasing. Rankings are existential (`Equiv.Perm (Fin n)`), equilibrium is the
position-deviation equilibrium (declared correction of p.6), efficiency means the ranking also
orders the values, and envy-freeness is (22) with the α-VCG payments. -/
theorem lemma_1 {k n : ℕ} (hkn : k ≤ n) {α β : ℕ → ℝ} (hα : IsPosVec k α) (hβ : IsPosVec k β)
    {v : Fin n → ℝ} (hv0 : ∀ i, 0 ≤ v i) (hv : Antitone v)
    (h : ∃ (b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),
      IsEfficientEquilibrium (payV k α) β v b σ) :
    ∃ (b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),
      IsEfficientEquilibrium (payV k α) β v b σ ∧ IsEnvyFree (payV k α) β v b σ := by sorry

end NontruthfulPA
