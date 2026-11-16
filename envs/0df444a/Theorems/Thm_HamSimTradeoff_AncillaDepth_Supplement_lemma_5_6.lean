-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_5_6
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:56:49.938231+00:00
-- url     : https://prove2.me/theorems/aa79cdb9-a2c9-458d-b072-fccc7b589d58
-- title:
--   Lemma 5.6 — degree-one constraints: ∑|c_j − λ_j|² ≤ ε², |1 − ∑c_j| ≤ ε, ∑(s_j − |c_j|) ≤ ε, ∑(√β_j − √γ_j)² ≤ 2ε
-- statement:
--   Fix an input-independent repeated-query circuit with $a$ ancilla qubits, $T$ queries, ancilla gates $V_0,\ldots,V_T$ and query labels $\alpha_t\in[L]$. Its success block $B(P)$ and target $A(P)=\sum_j\lambda_jP_j$ are defined by (1.16)–(1.17). Here $N\ge1$ is one fixed system dimension, $\lambda_j\ge0$, $\sum_j\lambda_j=1$, and $\varepsilon\ge0$. Use the canonical histories from the proof of Lemma 5.2: $W_j=V_{j-1}\cdots V_0$, $\psi_j=W_j^\dagger|0^a\rangle$, $u=W_{T+1}^\dagger|0^a\rangle$, $v=|0^a\rangle$, $\Pi_j=|\psi_j\rangle\langle\psi_j|$, $A_j=I-\Pi_j$. The amplitudes $x_j,y_j,h_{ij}$ are those of (5.4), $H_{ij}=h_{ij}$ for $i>j$ and zero otherwise, and $G$ is their Gram matrix. Assume the uniform error bound (1.17). Define $c_j=\sum_{\alpha_t=j}x_ty_t$, $\beta_j=\sum_{\alpha_t=j}|x_t|^2$, $\gamma_j=\sum_{\alpha_t=j}|y_t|^2$, and $s_j=\sqrt{\beta_j\gamma_j}$. Then
--   $$\sum_j|c_j-\lambda_j|^2\le\varepsilon^2,\quad\left|1-\sum_jc_j\right|\le\varepsilon,\quad\sum_j(s_j-|c_j|)\le\varepsilon,\quad\sum_j(\sqrt{\beta_j}-\sqrt{\gamma_j})^2\le2\varepsilon.$$
--   All four constraints are retained. They relate the degree-one response to the target coefficients.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: system dimension N of the input unitaries P_j in U(N) → hypothesis 1 ≤ N; reason: U(0) is the trivial group of empty matrices; N ≥ 1 only excludes the degenerate empty system space
--   - reading: §5 preamble (p.23): λ_j > 0 and ∑_j λ_j = 1; Theorem 5.1: λ_j ≥ 0 → ProbabilityWeights: λ_j ≥ 0 and ∑_j λ_j = 1; reason: the section preamble and Theorem 5.1 disagree on zero weights; the lemmas are read with Theorem 5.1's convention, which contains every positive-weight instance (not the weaker reading)
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 26, Lemma 5.6

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_5_6 {L N : ℕ} (hN : 1 ≤ N) (B : LCUCircuit L)
    (lam : Fin L → ℝ) (hlam : ProbabilityWeights lam) (eps : ℝ) (heps : 0 ≤ eps)
    (happrox : LCUApprox B N lam eps) :
    (∑ j, ‖degreeOne B j - (lam j : ℂ)‖^2) ≤ eps^2 ∧
    ‖(1:ℂ) - ∑ j, degreeOne B j‖ ≤ eps ∧
    (∑ j, (sWeight B j - ‖degreeOne B j‖)) ≤ eps ∧
    (∑ j, (Real.sqrt (beta B j) - Real.sqrt (gamma B j))^2) ≤ 2*eps := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
