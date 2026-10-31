-- Prove2me | Theorems.Thm_NontruthfulPA_envy_free_imp_equilibrium
-- name    : NontruthfulPA.envy_free_imp_equilibrium
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:20.863172+00:00
-- url     : https://prove2.me/theorems/bf54035c-b34a-49a7-afde-38c7ddc504a2
-- title:
--   p.11 — envy-freeness implies the equilibrium condition for $\alpha$-VCG and $\alpha$-GSP
-- statement:
--   There are $k$ positions and $n \ge k$ bidders. The position vectors $\alpha, \beta \in \mathbb R^k_\ge$ are positive and non-increasing, with $\alpha_j = \beta_j = 0$ for $j > k$; bidder $i$ values position $j$ at $\beta_j v_i$ with $v_i \ge 0$. Bids are $b \in [0,\infty)^n$, and $b_{(t)}$ denotes the $t$-th highest bid, with $b_{(t)} = 0$ for $t > n$.
--
--   Let $b \ge 0$ be a bid profile and $\sigma$ an allocation that orders it. Then:
--
--   1. if $(b, \sigma)$ is envy-free (22) under the $\alpha$-VCG payments, it is an equilibrium of the $\alpha$-VCG mechanism;
--   2. if $(b, \sigma)$ is envy-free (22) under the $\alpha$-GSP payments, it is an equilibrium of the $\alpha$-GSP mechanism.
--
--   In both mechanisms the current payment of a position is a lower bound on what a bidder pays when it moves to that position. Since envy-freeness depends only on the allocation and the payments, this is how the proof of Theorem 1 transfers equilibria between the two mechanisms.
--
--   **Formalization Note** Bidders are `Fin n` and positions are 0-based ranks (rank $r$ is position $r+1$); $\alpha, \beta$ are functions on $\mathbb N$ that vanish from index $k$ on; the bids in rank order are padded by $0$ past rank $n$. Equilibrium is the position-deviation equilibrium of the mission's model.
--
--   Differences from the source:
--   - reading: (Nash) equilibrium: p.6 allows every real deviation x under a fixed tie-breaking allocation; §3.1 (p.8) and §3.2 (p.11) describe it as a bidder raising or lowering its bid and being assigned a different position → IsPDEquilibrium: for every bidder i and every position r, moving i to r (others keep their order) at the price the mechanism charges on the deviated rank list does not raise i's utility; ties are resolved by the ranking σ; reason: §3's own notion; the mission uses it throughout because the main theorem is false under the p.6 notion (see Theorem 1)
--   - reading: bid profiles b ∈ ℝ^n (p.6) → bids b_i ≥ 0; reason: mechanisms charge non-negative payments (p.6) and §3.1 uses b_3 ≥ 0 (p.8); with negative bids the payments could be negative
--   - reading: v ∈ ℝ^n with β_j v_i ≥ 0 the value for position j (p.6) → v_i ≥ 0; reason: β_j > 0 for j ≤ k, so β_j v_i ≥ 0 is v_i ≥ 0
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, §3.2, p.11, "For both the α-VCG mechanism and the α-GSP mechanism envy-freeness implies the equilibrium condition"

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- **Envy-freeness implies the equilibrium condition**, Dütting–Fischer–Parkes, *Non-Truthful
Position Auctions Are More Robust to Misspecification*, arXiv:1602.07593v4, §3.2, p.11: "For
both the α-VCG mechanism and the α-GSP mechanism envy-freeness implies the equilibrium condition
because the current payment is a lower bound on the actual payment of the bidder if by either
mechanism it was assigned that position."

For any non-negative bid profile `b` and any ranking `σ` that orders it (an allocation of the
rule `g`), envy-freeness (22) under the α-VCG payments implies that `b` is an α-VCG equilibrium,
and envy-freeness under the α-GSP payments implies that `b` is an α-GSP equilibrium.

**Formalization Note.** Equilibrium is the position-deviation equilibrium `IsPDEquilibrium`
(declared correction of p.6); ranks are 0-based. -/
theorem envy_free_imp_equilibrium {k n : ℕ} (hkn : k ≤ n) {α β : ℕ → ℝ} (hα : IsPosVec k α)
    (hβ : IsPosVec k β) {v b : Fin n → ℝ} (hv0 : ∀ i, 0 ≤ v i) {σ : Equiv.Perm (Fin n)}
    (hb0 : ∀ i, 0 ≤ b i) (hσ : Orders σ b) :
    (IsEnvyFree (payV k α) β v b σ → IsPDEquilibrium (payV k α) β v b σ) ∧
      (IsEnvyFree (payS α) β v b σ → IsPDEquilibrium (payS α) β v b σ) := by sorry

end NontruthfulPA
