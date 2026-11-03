-- Prove2me | Theorems.Thm_IncentiveFinNet_best_response
-- name    : IncentiveFinNet.best_response
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:53.488633+00:00
-- url     : https://prove2.me/theorems/e4e13993-03b9-4bac-8b9c-e051f96f4f09
-- title:
--   A.1: each agent's unique best response to prices is $Q_j(M-P)e_j$
-- statement:
--   Fix a network setting $(\mu_i, \gamma_i, \Sigma_i, \Psi_i)_{i\in[n]}$ with expected-return matrix $M$, utilities $g_i$ and $Q_i = \Psi_i^{\top}(2\gamma_i\Psi_i\Sigma_i\Psi_i^{\top})^{-1}\Psi_i$. Let $P$ be any $n\times n$ price matrix, let $j$ be an agent, and let
--   $$
--   b = Q_j (M - P) e_j \in \mathbb R^n
--   $$
--   be the $j$-th column of the best-response network. Then:
--
--   1. $b_k = 0$ for every $k \notin J_j$;
--   2. for every $n\times n$ matrix $W'$ whose $j$-th column vanishes outside $J_j$, $g_j(W', P) \le g_j(W^{\mathrm{BR}}, P)$, where $W^{\mathrm{BR}}$ is the best-response network (its $j$-th column is $b$);
--   3. equality holds only if the $j$-th column of $W'$ equals $b$.
--
--   So agent $j$'s utility-maximizing contract sizes at prices $P$, subject to its permitted counterparties, are unique and given by
--   $$
--   W_{ij} = e_i^{\top}\Psi_j^{\top}(2\gamma_j\Psi_j\Sigma_j\Psi_j^{\top})^{-1}\Psi_j(M-P)e_j = e_i^{\top}Q_j(M-P)e_j .
--   $$
--   This is the first step of the proof of Theorem 1: a stable network must be the best-response network at its prices.
--
--   **Formalization Note** $g_j(W',P)$ depends on $W'$ only through its $j$-th column, so the maximization over columns is written over matrices $W'$.
--
--   Differences from the source:
--   - generalization: for any price matrix P with P = −Pᵀ → for every price matrix P; reason: the best-response formula does not use skew-symmetry, and the source's case is the special case of a skew-symmetric P
--   - reading: the jth column has the utility-maximizing contract sizes for agent j → the column vanishes outside J_j, maximizes g_j among all W′ whose column j vanishes outside J_j, and is the unique maximizer; reason: these are agent j's constraints under Definition 2 (any such column extends to a feasible W′ by the symmetry of the J_i), and the proof uses the maximizer as unique
--   - reading: if k ∉ J_i (and hence i ∉ J_k) → the setting assumes k ∈ J_i ↔ i ∈ J_k; reason: the parenthetical states the symmetry of the permitted sets
--   - encoding: Σ_j ≻ 0, agents [n], rows of Ψ_j indexed by positions in the ordered set J_j → Matrix.PosDef (symmetric), Fin n, rows indexed by the elements of J_j; reason: Lean conventions; the order of J_j does not change Q_j
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, A.1 (Proof of Theorem 1), best-response display, p.33

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Q

open Matrix

namespace IncentiveFinNet

/-- **A.1, best-response display**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, p.33:
for prices `P`, agent `j`'s utility-maximizing contract sizes are
`W_ij = e_iᵀ Ψ_jᵀ (2γ_j Ψ_j Σ_j Ψ_jᵀ)⁻¹ Ψ_j (M − P) e_j = e_iᵀ Q_j (M − P) e_j`.

Stated for every agent `j` and every price matrix `P`: the column `j` of `bestResponse S P`
(1) vanishes outside `J_j`; (2) gives agent `j` at least the utility of any `W′` whose column `j`
vanishes outside `J_j`; (3) is the unique such maximizer.

**Formalization Note** `g_j(W′, P)` depends on `W′` only through its column `j`, so the
maximization over columns is stated through matrices `W′`. The skew-symmetry `P = −Pᵀ` of the
page is not needed and not assumed. -/
theorem best_response {n : ℕ} (S : NetworkSetting n) (P : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : (∀ k, k ∉ S.J j → bestResponse S P k j = 0) ∧ ∀ W' : Matrix (Fin n) (Fin n) ℝ, (∀ k, k ∉ S.J j → W' k j = 0) → S.utility j W' P ≤ S.utility j (bestResponse S P) P ∧ (S.utility j W' P = S.utility j (bestResponse S P) P → ∀ k, W' k j = bestResponse S P k j) := by sorry

end IncentiveFinNet
