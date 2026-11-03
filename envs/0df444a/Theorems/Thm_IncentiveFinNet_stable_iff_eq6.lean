-- Prove2me | Theorems.Thm_IncentiveFinNet_stable_iff_eq6
-- name    : IncentiveFinNet.stable_iff_eq6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:55.339249+00:00
-- url     : https://prove2.me/theorems/b9fa012b-348d-42ae-8302-e42247b23d8d
-- title:
--   A.1, (5)–(6): stability is equivalent to the symmetry conditions (6) on the best-response network
-- statement:
--   Fix a network setting $(\mu_i, \gamma_i, \Sigma_i, \Psi_i)_{i\in[n]}$ with expected-return matrix $M$, matrices $Q_i$, and $A_{ij} = e_i^{\top}Q_jMe_j$. For $n\times n$ matrices $W$ and $P$, the pair $(W,P)$ is a stable point if and only if all of the following hold:
--
--   1. $P = -P^{\top}$, and $P_{ik} = 0$ whenever $k \notin J_i$;
--   2. $W$ is the best-response network at $P$: $W_{ij} = e_i^{\top}Q_j(M-P)e_j$ for all $i,j$;
--   3. for all $i < j$,
--   $$
--   e_i^{\top}(A - A^{\top})e_j = e_i^{\top}\bigl(Q_jP - (Q_iP)^{\top}\bigr)e_j. \tag{6}
--   $$
--
--   Condition (6) is the symmetry condition $W_{ij} = W_{ji}$ (5) of the best-response network, rewritten with $A$. It reduces the existence of a stable point to a linear system in the prices.
--
--   Differences from the source:
--   - reading: The tuple (W,P) is stable if W = Wᵀ. So, for all i < j, we require (5) ⇔ … ⇔ (6) → (W,P) is stable iff P is skew-symmetric and vanishes on prohibited pairs, W is the best-response network at P, and (6) holds for all i < j; reason: this is the equivalence the proof establishes and uses, with W the best-response matrix of the preceding display
--   - reading: W and P obey the constraints encoded in (Ψ_i) (Definition 2) → k ∉ J_i implies W_ik = 0 and P_ik = 0; reason: the p.9 sentence "if k ∉ J_i (and hence i ∉ J_k), we have W_ik = W_ki = P_ik = P_ki = 0", together with the symmetry of J, W and −P
--   - reading: g_i(W,P) = max over feasible (W′,P) of g_i(W′,P) (Definition 3) → g_i(W′,P) ≤ g_i(W,P) for every feasible (W′,P); reason: equivalent because (W,P) is itself feasible
--   - reading: if k ∉ J_i (and hence i ∉ J_k) → the setting assumes k ∈ J_i ↔ i ∈ J_k; reason: the parenthetical states the symmetry of the permitted sets
--   - encoding: Σ_i ≻ 0, agents [n] → Matrix.PosDef (symmetric), Fin n; reason: Lean conventions
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, A.1 (Proof of Theorem 1), equations (5)–(6), p.33; Definitions 2–3, p.10

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Q
import Definitions.Def_IncentiveFinNet_ZF

open Matrix

namespace IncentiveFinNet

/-- **A.1, (5)–(6)**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, p.33: "The tuple `(W, P)` is
stable if `W = Wᵀ`. So, for all `i < j`, we require `W_ij = W_ji` (5) `⇔ … ⇔
e_iᵀ(A − Aᵀ)e_j = e_iᵀ(Q_j P − (Q_i P)ᵀ)e_j` (6)."

Stated as the characterization the proof establishes: `(W, P)` is stable iff `P` is
skew-symmetric and vanishes on prohibited pairs, `W` is the best-response matrix
`W_ij = e_iᵀ Q_j (M − P) e_j`, and (6) holds for all `i < j`. -/
theorem stable_iff_eq6 {n : ℕ} (S : NetworkSetting n) (W P : Matrix (Fin n) (Fin n) ℝ) : Stable S W P ↔ (Pᵀ = -P ∧ (∀ i k, k ∉ S.J i → P i k = 0) ∧ W = bestResponse S P ∧ ∀ i j : Fin n, i < j → (matA S - (matA S)ᵀ) i j = (Q S j * P - (Q S i * P)ᵀ) i j) := by sorry

end IncentiveFinNet
