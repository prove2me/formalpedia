-- Prove2me | Theorems.Thm_MultPacing_Existence_theorem_1_payments
-- name    : MultPacing.Existence.theorem_1_payments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:02.077489+00:00
-- url     : https://prove2.me/theorems/03792b05-5c5b-4534-b0c8-b513026cc303
-- title:
--   Proof of Theorem 1, "The payments are right", p. 12 — limit prices are the highest other limit bids and s*_ij = x*_ij p*_ij
-- statement:
--   In the setting of the proof of Theorem 1 (a convergent sequence of equilibria $\alpha^l$ of $(\epsilon^l,H^l)$-smoothed pacing games with $\epsilon^l\to0$, $H^l\to\infty$, $H^l>M/\epsilon^l$, and limits $\alpha^*,x^*,p^*,s^*$ of the multipliers, allocations, prices and payments), for every buyer $i$ and good $j$:
--   $$
--   p^*_{ij}=\max_{k\ne i}\alpha^*_k v_{kj}\qquad\text{and}\qquad s^*_{ij}=x^*_{ij}\,p^*_{ij},
--   $$
--   where the maximum is $0$ when $i$ is the only buyer. So the limit price is the second price of the limit bids, and the limit payment is price times allocation.
--
--   **Formalization Note** The limit price is indexed by buyer and good ($p^*_{ij}$), as the smoothed price is; that the winners of a good see the same price follows from this claim together with the tie condition of the previous claim.
--
--   Differences from the source:
--   - reading: the limit price $p^*_j=\lim_l p^l_j$, where $p^l_j$ is "the highest bid on $j$ among buyers other than $i$, minus $\epsilon$" → a price $p^*_{ij}$ for each buyer and good; reason: Definition 3's $p_j$ depends on $i$.
--   - encoding: "the highest other bid at the limit point" → `highestOther`, the maximum over $k\ne i$, $0$ if there is no other buyer; reason: the reserve bid $2\epsilon^l$ tends to $0$, and the paper gives a lone bidder price $0$ (p. 16).
--   - encoding: convergence of a subsequence → convergence of the sequence; reason: the paper replaces the sequence by the subsequence before the claims.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 12 (PDF 12), proof of Theorem 1, claim "The payments are right"

import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

namespace MultPacing.Existence

theorem theorem_1_payments {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ)
    (xs ps ss : N → G → ℝ) (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) :
    (∀ i j, ps i j = highestOther P.v αs i j) ∧ (∀ i j, ss i j = xs i j * ps i j) := by sorry

end MultPacing.Existence
