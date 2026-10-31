-- Prove2me | Theorems.Thm_NontruthfulPA_pessimal_profile
-- name    : NontruthfulPA.pessimal_profile
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:12.43309+00:00
-- url     : https://prove2.me/theorems/68f0818f-639e-4808-9b62-3db8264be371
-- title:
--   (26)–(27) — the bidder-pessimal profile is an efficient $\alpha$-VCG equilibrium satisfying (27)
-- statement:
--   There are $k$ positions and $n \ge k$ bidders. The position vectors $\alpha, \beta \in \mathbb R^k_\ge$ are positive and non-increasing, with $\alpha_j = \beta_j = 0$ for $j > k$; bidder $i$ values position $j$ at $\beta_j v_i$ with $v_i \ge 0$. Bids are $b \in [0,\infty)^n$, and $b_{(t)}$ denotes the $t$-th highest bid, with $b_{(t)} = 0$ for $t > n$.
--
--   Assume $v_1 \ge \dots \ge v_n$ and let $b$ be an equilibrium of the $\alpha$-VCG mechanism with bidder $i$ in position $i$ (so $b_1 \ge \dots \ge b_n \ge 0$, and the equilibrium is efficient). Let $\hat b$ be the bidder-pessimal profile (26) built from $b$. Then
--
--   1. $\hat b_1 \ge \dots \ge \hat b_n$;
--   2. $b_i \le \hat b_i$ for every $i$;
--   3. $\hat b$ is again an equilibrium of the $\alpha$-VCG mechanism with bidder $i$ in position $i$, hence an efficient one;
--   4. for all $i \in \{2, \dots, n\}$,
--   $$(\alpha_{i-1} - \alpha_i)\, \hat b_i \ \ge\ (\beta_{i-1} - \beta_i)\, v_i. \tag{27}$$
--
--   Since $\hat b$ depends on $b$ only through $b_1$, item 2 says that each of the bids $\hat b_2, \dots, \hat b_n$ is maximal among efficient equilibria with the same top bid. Condition (27) is the special case $j = i-1$ of (25).
--
--   **Formalization Note** Bidders are `Fin n` and positions are 0-based ranks (rank $r$ is position $r+1$); $\alpha, \beta$ are functions on $\mathbb N$ that vanish from index $k$ on; the bids in rank order are padded by $0$ past rank $n$. Equilibrium is the position-deviation equilibrium of the mission's model.
--
--   Differences from the source:
--   - reading: (Nash) equilibrium: p.6 allows every real deviation x under a fixed tie-breaking allocation; §3.1 (p.8) and §3.2 (p.11) describe it as a bidder raising or lowering its bid and being assigned a different position → IsPDEquilibrium: for every bidder i and every position r, moving i to r (others keep their order) at the price the mechanism charges on the deviated rank list does not raise i's utility; ties are resolved by the ranking σ; reason: §3's own notion; the mission uses it throughout because the main theorem is false under the p.6 notion (see Theorem 1)
--   - reading: bid profiles b ∈ ℝ^n (p.6) → bids b_i ≥ 0; reason: mechanisms charge non-negative payments (p.6) and §3.1 uses b_3 ≥ 0 (p.8); with negative bids the payments could be negative
--   - reading: v ∈ ℝ^n with β_j v_i ≥ 0 the value for position j (p.6) → v_i ≥ 0; reason: β_j > 0 for j ≤ k, so β_j v_i ≥ 0 is v_i ≥ 0
--   - encoding: WLOG v_1 ≥ ⋯ ≥ v_n and bidder i is assigned position i (p.11) → v and b antitone on Fin n and the identity ranking Equiv.refl; reason: the paper's sorted frame, written out
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, proof of Lemma 1, (26)–(27), p.12

import Mathlib
import Definitions.Def_NontruthfulPA_Model
import Definitions.Def_NontruthfulPA_PessimalProfile

namespace NontruthfulPA

/-- **The bidder-pessimal profile (26) is an efficient α-VCG equilibrium satisfying (27)**,
Dütting–Fischer–Parkes, *Non-Truthful Position Auctions Are More Robust to Misspecification*,
arXiv:1602.07593v4, proof of Lemma 1, p.12: "Bid b_i, for i ∈ {2,…,n}, thus is subject to only
two upper bounds on, b_i ≤ b_{i−1} by efficiency and (α_{i−1} − α_i) b_i ≤ (β_{i−1} − β_i) v_{i−1}
by (24). Increasing each of these bids as much as possible yields a bid profile b such for all
i ∈ {2,…,n}, (26) … We now claim that b satisfies (25) and begin by showing this for the special
case where j = i − 1, which requires that for all i ∈ {2,…,n},
(α_{i−1} − α_i) b_i ≥ (β_{i−1} − β_i) v_i. (27)"

In the sorted frame (values non-increasing, identity ranking): if `b` is an efficient α-VCG
equilibrium, then the profile `b̂ = pessimal α β v b` of (26) is non-increasing, dominates `b`
bid by bid, is again an α-VCG equilibrium (efficient, as it is sorted like `v`), and satisfies
(27) for every `i ∈ {2, …, n}`.

**Formalization Note.** 0-based: the index `i + 1` here is the paper's `i + 2`, so (27) reads
`(β i − β (i+1)) v_{i+1} ≤ (α i − α (i+1)) b̂_{i+1}` for `i + 1 < n`. `b̂` depends on `b` only
through `b_1`, so `∀ i, b i ≤ b̂ i` applied to any efficient equilibrium with the same top bid is
the page's maximality of `b̂`. Equilibrium is the position-deviation equilibrium. -/
theorem pessimal_profile {k n : ℕ} (hkn : k ≤ n) {α β : ℕ → ℝ} (hα : IsPosVec k α)
    (hβ : IsPosVec k β) {v b : Fin n → ℝ} (hv0 : ∀ i, 0 ≤ v i) (hv : Antitone v)
    (hNE : IsPDEquilibrium (payV k α) β v b (Equiv.refl (Fin n))) :
    Antitone (pessimal α β v b) ∧ (∀ i, b i ≤ pessimal α β v b i) ∧
      IsPDEquilibrium (payV k α) β v (pessimal α β v b) (Equiv.refl (Fin n)) ∧
      ∀ (i : ℕ) (h : i + 1 < n),
        (β i - β (i + 1)) * v ⟨i + 1, h⟩ ≤ (α i - α (i + 1)) * pessimal α β v b ⟨i + 1, h⟩ := by sorry

end NontruthfulPA
