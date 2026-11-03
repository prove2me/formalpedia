-- Prove2me | Theorems.Thm_IncentiveFinNet_disallowed_edges
-- name    : IncentiveFinNet.disallowed_edges
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:49.672676+00:00
-- url     : https://prove2.me/theorems/53ae984f-093a-4433-a833-eb6f3a2bfa0a
-- title:
--   A.1 part (2), disallowed edges: the system (6) reduces to $Z_F\,\mathrm{uvec}(P)_F = \mathrm{uvec}(A-A^{\top})_F$
-- statement:
--   Fix a network setting $(\mu_i, \gamma_i, \Sigma_i, \Psi_i)_{i\in[n]}$ with matrices $Q_i$, $A$, $B_{(i,j)}$, $C_{(i,j)}$, the permitted pairs $F$ and the matrix $Z_F$ of Theorem 1.
--
--   1. **Prohibited edges contribute nothing.** If $\{i,j\}$ is a prohibited edge ($j \notin J_i$), then $B_{(i,j)} = B_{(j,i)} = 0$, hence $C_{(i,j)} = 0$ (the row of $Z$ indexed by $(i,j)$ vanishes), and $A_{ij} = A_{ji} = 0$, hence $(A - A^{\top})_{ij} = 0$.
--   2. **Reduced system.** For every price matrix $P$ with $P = -P^{\top}$ and $P_{ik} = 0$ whenever $k \notin J_i$, the conditions
--   $$
--   e_i^{\top}(A - A^{\top})e_j = e_i^{\top}\bigl(Q_jP - (Q_iP)^{\top}\bigr)e_j \qquad\text{for all } i < j \tag{6}
--   $$
--   hold if and only if
--   $$
--   Z_F\,\mathrm{uvec}(P)_F = \mathrm{uvec}(A - A^{\top})_F .
--   $$
--   3. **Solutions are prices.** Every vector $p_F \in \mathbb R^{|F|}$ is $\mathrm{uvec}(P)_F$ for exactly one matrix $P$ with $P = -P^{\top}$ and $P_{ik} = 0$ whenever $k \notin J_i$.
--
--   Together with the trace identity, this shows that the linear system of the proof of Theorem 1 is equivalent to the unconstrained reduced system $Z_Fp_F = \mathrm{uvec}(A-A^{\top})_F$, each of whose solutions is the price vector of a skew-symmetric price matrix.
--
--   Differences from the source:
--   - reading: If {i,j} is a prohibited edge then … so e_ijᵀZ = 0ᵀ … Aij = Aji = 0 so uvec(A − Aᵀ)ij = 0 → j ∉ J_i implies B_(i,j) = B_(j,i) = 0, C_(i,j) = 0, A_ij = A_ji = 0 and (A − Aᵀ)_ij = 0; reason: e_ijᵀZ is the row uvec(C_(i,j)) of the full matrix Z, which vanishes exactly when C_(i,j) does above the diagonal; C_(i,j) = 0 states it for the whole matrix
--   - reading: the linear system in (1) is equivalent to the (unconstrained) reduced system Z_F p_F = uvec(A − Aᵀ)_F → for every skew-symmetric P vanishing on prohibited pairs, (6) for all i < j holds iff Z_F uvec(P)_F = uvec(A − Aᵀ)_F; reason: the system of part (1) is (6) for all i < j, constrained by p_ij = 0 on prohibited pairs; its rewriting through uvec is the trace identity, stated as a separate milestone
--   - reading: Each solution p_F corresponds to a skew-symmetric P by construction → every p_F is uvec(P)_F for exactly one skew-symmetric P vanishing on prohibited pairs; reason: the correspondence P = R − Rᵀ, p = uvec(R) of part (1), restricted to F
--   - reading: if k ∉ J_i (and hence i ∉ J_k) → the setting assumes k ∈ J_i ↔ i ∈ J_k; reason: the parenthetical states the symmetry of the permitted sets
--   - encoding: prohibited edge {i,j} (Ψ_i e_j = 0), vectors in ℝ^|F| listed in the order of F → j ∉ J_i, functions on the subtype F; reason: Ψ_i e_j = 0 iff j ∉ J_i; the order of F does not change the system
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, A.1 (Proof of Theorem 1), part (2) Disallowed edges, p.34

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_matC
import Definitions.Def_IncentiveFinNet_Q
import Definitions.Def_IncentiveFinNet_ZF

open Matrix

namespace IncentiveFinNet

/-- **A.1 part (2), "Disallowed edges"**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, p.34.

1. If `{i, j}` is a prohibited edge (`j ∉ J_i`), then `B_{(i,j)} = B_{(j,i)} = 0`, so
   `C_{(i,j)} = 0` (the row `(i, j)` of `Z` vanishes), and `A_ij = A_ji = 0`, so
   `uvec(A − Aᵀ)_{ij} = 0`.
2. For every skew-symmetric `P` vanishing on prohibited pairs, the system (6) for all `i < j` is
   equivalent to the reduced system `Z_F uvec(P)_F = uvec(A − Aᵀ)_F`.
3. Every `p_F ∈ ℝ^F` is `uvec(P)_F` for exactly one skew-symmetric `P` vanishing on prohibited
   pairs ("Each solution `p_F` corresponds to a skew-symmetric `P` by construction"). -/
theorem disallowed_edges {n : ℕ} (S : NetworkSetting n) : (∀ i j : Fin n, j ∉ S.J i → matB (Q S) i j = 0 ∧ matB (Q S) j i = 0 ∧ matC (Q S) i j = 0 ∧ matA S i j = 0 ∧ matA S j i = 0 ∧ (matA S - (matA S)ᵀ) i j = 0) ∧ (∀ P : Matrix (Fin n) (Fin n) ℝ, Pᵀ = -P → (∀ i k, k ∉ S.J i → P i k = 0) → ((∀ i j : Fin n, i < j → (matA S - (matA S)ᵀ) i j = (Q S j * P - (Q S i * P)ᵀ) i j) ↔ ZF S *ᵥ uvecF S P = uvecF S (matA S - (matA S)ᵀ))) ∧ ∀ p : PermittedPairs S → ℝ, ∃! P : Matrix (Fin n) (Fin n) ℝ, Pᵀ = -P ∧ (∀ i k, k ∉ S.J i → P i k = 0) ∧ uvecF S P = p := by sorry

end IncentiveFinNet
