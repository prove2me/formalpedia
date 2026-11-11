-- Prove2me | Theorems.Thm_IncentiveFinNet_theorem_1
-- name    : IncentiveFinNet.theorem_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:19:46.22527+00:00
-- url     : https://prove2.me/theorems/8f1e7b53-0514-4d21-8c8c-bec7bca2acd5
-- title:
--   Theorem 1 (Existence and Uniqueness of Stable Point), Expanded Version
-- statement:
--   Fix a network setting $(\mu_i, \gamma_i, \Sigma_i, \Psi_i)_{i\in[n]}$: $n$ agents, an expected-return matrix $M \in \mathbb R^{n\times n}$ whose $i$-th column is $\mu_i$, risk aversions $\gamma_i > 0$, covariance matrices $\Sigma_i \succ 0$ (one per agent), and permitted counterparty sets $J_i$ with $k \in J_i \iff i \in J_k$. Let $Q_i = \Psi_i^{\top}(2\gamma_i\Psi_i\Sigma_i\Psi_i^{\top})^{-1}\Psi_i$, let $F = \{(i,j) : 1 \le i < j \le n,\ \Psi_ie_j \ne 0\}$, and define the $n\times n$ matrices
--   $$
--   A_{ij} = e_i^{\top}Q_jMe_j, \qquad B_{(i,j)} = e_ie_j^{\top}Q_i, \qquad C_{(i,j)} = \bigl(B_{(i,j)} - B_{(j,i)}\bigr) - \bigl(B_{(i,j)} - B_{(j,i)}\bigr)^{\top}.
--   $$
--   Let $Z_F$ be the $|F|\times|F|$ matrix whose rows are $\mathrm{uvec}(C_{(i,j)})_F$, $(i,j) \in F$. Then:
--
--   1. a stable point $(W,P)$ exists if and only if $\mathrm{uvec}(A - A^{\top})_F$ lies in the column space of $Z_F$;
--   2. every stable point $(W,P)$ satisfies
--   $$
--   Z_F\,\mathrm{uvec}(P)_F = \mathrm{uvec}(A - A^{\top})_F ;
--   $$
--   3. if $Z_F$ has full rank, there is exactly one stable point $(W,P)$.
--
--   Here a stable point is a pair $(W, P)$ with $W$ symmetric, $P$ skew-symmetric, both zero on prohibited pairs, such that no agent can raise its mean-variance utility $g_i(W', P) = w_i'^{\top}(\mu_i - Pe_i) - \gamma_i w_i'^{\top}\Sigma_i w_i'$ by changing to another feasible network $W'$ at the same prices.
--
--   The theorem turns a fixed-point question about selfish agents into linear algebra: the existence of stable contracts and prices is the solvability of one linear system in the prices, and uniqueness follows from the invertibility of its matrix.
--
--   **Formalization Note** The column space of $Z_F$ is the range of the linear map $p \mapsto Z_Fp$; full rank of the square matrix $Z_F$ is $\operatorname{rank} Z_F = |F|$; uniqueness in part 3 is uniqueness of the pair $(W,P)$. Every $n$ is covered, including $n = 0$ and settings with $F = \emptyset$, where $Z_F$ is the empty matrix and has full rank.
--
--   Differences from the source:
--   - reading: if k ∉ J_i (and hence i ∉ J_k) → the setting assumes k ∈ J_i ↔ i ∈ J_k; reason: the parenthetical states the symmetry of the permitted sets
--   - reading: W and P obey the constraints encoded in (Ψ_i) (Definition 2) → k ∉ J_i implies W_ik = 0 and P_ik = 0; reason: the p.9 sentence "if k ∉ J_i (and hence i ∉ J_k), we have W_ik = W_ki = P_ik = P_ki = 0", together with the symmetry of J, W and −P
--   - reading: g_i(W,P) = max over feasible (W′,P) of g_i(W′,P) (Definition 3) → g_i(W′,P) ≤ g_i(W,P) for every feasible (W′,P); reason: equivalent because (W,P) is itself feasible
--   - encoding: agents [n], ordered sets J_i and F, vectors in ℝ^|F|, the |F| × |F| matrix Z_F → Fin n, Finset J_i, the subtype F of pairs, functions on F and a matrix indexed by F × F; reason: Lean conventions; the orders of J_i and F change no quantity of the theorem
--   - encoding: Σ_i ≻ 0 → Matrix.PosDef (symmetric); reason: a covariance matrix is symmetric
--   - encoding: column space of Z_F; Z_F is full rank; a unique stable point exists → LinearMap.range of Z_F.mulVecLin; rank Z_F = card F; ∃! of the pair (W, P); reason: standard Lean forms of the same notions
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 1 (Existence and Uniqueness of Stable Point), pp.11–12; Expanded Version of Theorem 1, A.1, p.33; Definitions 1–3, p.10

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_matC
import Definitions.Def_IncentiveFinNet_Q
import Definitions.Def_IncentiveFinNet_ZF

open Matrix

namespace IncentiveFinNet

/-- **Theorem 1 (Existence and Uniqueness of Stable Point)**, Expanded Version, Jalan,
Chakrabarti, Sarkar, *Incentive-Aware Models of Financial Networks*, arXiv:2212.06808v3,
pp.11–12; Expanded Version, A.1, p.33.

With `A_ij = e_iᵀ Q_j M e_j`, `B_{(i,j)} = e_i e_jᵀ Q_i`,
`C_{(i,j)} = (B_{(i,j)} − B_{(j,i)}) − (B_{(i,j)} − B_{(j,i)})ᵀ`, and `Z_F` the `|F| × |F|` matrix
with rows `uvec(C_{(i,j)})_F`, `(i, j) ∈ F`:
1. a stable point `(W, P)` exists iff `uvec(A − Aᵀ)_F` lies in the column space of `Z_F`;
2. every stable point satisfies `Z_F uvec(P)_F = uvec(A − Aᵀ)_F`;
3. if `Z_F` has full rank, a stable point exists and is unique.

**Formalization Note** The column space of `Z_F` is `LinearMap.range Z_F.mulVecLin`; "full rank"
for the square matrix `Z_F` is `rank Z_F = |F|`; uniqueness is of the pair `(W, P)`. -/
theorem theorem_1 {n : ℕ} (S : NetworkSetting n) : ((∃ W P : Matrix (Fin n) (Fin n) ℝ, Stable S W P) ↔ uvecF S (matA S - (matA S)ᵀ) ∈ LinearMap.range (ZF S).mulVecLin) ∧ (∀ W P : Matrix (Fin n) (Fin n) ℝ, Stable S W P → ZF S *ᵥ uvecF S P = uvecF S (matA S - (matA S)ᵀ)) ∧ ((ZF S).rank = Fintype.card (PermittedPairs S) → ∃! WP : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ, Stable S WP.1 WP.2) := by sorry

end IncentiveFinNet
