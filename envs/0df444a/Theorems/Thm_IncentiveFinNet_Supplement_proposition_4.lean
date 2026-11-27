-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_proposition_4
-- name    : IncentiveFinNet.Supplement.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:35:39.115124+00:00
-- url     : https://prove2.me/theorems/44550b79-a690-4153-ac02-5c02a613a657
-- title:
--   Proposition 4 — price after a pairwise negotiation
-- statement:
--   Consider a network setting and a skew-symmetric price matrix $P=-P^{\top}$, and let $(i,j)$ be a pair of agents permitted to trade ($j\in J_i$). Let $P'$ be another skew-symmetric price matrix such that
--
--   1. $P'$ differs from $P$ only in the cells $(i,j)$ and $(j,i)$, and
--   2. under $P'$, when $i$ and $j$ choose their optimal contract sizes with all agents, $i$'s optimal contract with $j$ equals $j$'s optimal contract with $i$: $e_j^{\top}Q_i(M-P')e_i = e_i^{\top}Q_j(M-P')e_j$.
--
--   Then
--   $$
--   P'_{ij} = \frac{e_i^{\top}Q_j(M-P)e_j - e_j^{\top}Q_i(M-P)e_i}{Q_{i;j,j}+Q_{j;i,i}} + P_{ij}.
--   $$
--
--   This is the price two agents agree on in one round of pairwise negotiations (Algorithm 1); it is the update whose dynamics Theorem 9 linearizes.
--
--   Differences from the source:
--
--   - reading: conditions (b) "i and j both maximize their utility at the same contract size under P′" and (c) "i and j can choose their optimal contract sizes with all other agents given these prices" → bestResponse S P′ j i = bestResponse S P′ i j; reason: under (c) each of i, j plays its utility-maximizing contract vector given P′, which is the corresponding column of the best-response matrix W_ab = e_aᵀQ_b(M − P′)e_b (A.1, p.33; unique by the base milestone IncentiveFinNet.best_response); (b) equates w_{i;j} and w_{j;i}
--   - encoding: "(i, j) permitted to trade"; e_iᵀXe_j → j ∈ S.J i; the entry X i j; reason: Lean convention; same pairs
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Proposition 4 (Price after Pairwise Negotiation), A.7, p.38

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Q

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Proposition 4 (Price after Pairwise Negotiation)**, Jalan, Chakrabarti, Sarkar,
arXiv:2212.06808v3, A.7, p.38: "Given a price matrix `P = −Pᵀ` and a pair of firms `(i, j)` that
are permitted to trade, let `P′` be another skew-symmetric price matrix such that (a) `P′` differs
from `P` only in the cells `(i, j)` and `(j, i)`, (b) `i` and `j` both maximize their utility at the
same contract size under `P′`, and (c) `i` and `j` can choose their optimal contract sizes with all
other agents given these prices. Then,
`P′_ij = (e_iᵀ Q_j (M − P) e_j − e_jᵀ Q_i (M − P) e_i) / (Q_{i;j,j} + Q_{j;i,i}) + P_ij`."

**Formalization Note**
* "Permitted to trade" is `j ∈ J_i`.
* Under (c) each of `i`, `j` plays its utility-maximizing contract vector given `P′`, which is the
  column of the published best-response matrix `bestResponse S P′` (`W_ab = e_aᵀ Q_b (M − P′) e_b`,
  A.1, p.33; unique by the base milestone `IncentiveFinNet.best_response`). Condition (b), "the same
  contract size", is then `w_{i;j} = w_{j;i}`, i.e. `bestResponse S P′ j i = bestResponse S P′ i j`.
* `e_iᵀ X e_j` is the entry `X i j`. -/
theorem proposition_4 {n : ℕ} (S : NetworkSetting n) (P P' : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = -P) (i j : Fin n) (hij : j ∈ S.J i) (hP' : P'ᵀ = -P')
    (ha : ∀ a b, ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i)) → P' a b = P a b)
    (hbc : bestResponse S P' j i = bestResponse S P' i j) :
    P' i j = ((Q S j * (S.M - P)) i j - (Q S i * (S.M - P)) j i) /
        ((Q S i) j j + (Q S j) i i) + P i j := by sorry

end IncentiveFinNet.Supplement
