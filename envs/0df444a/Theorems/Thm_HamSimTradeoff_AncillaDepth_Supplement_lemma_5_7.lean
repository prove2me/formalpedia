-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_5_7
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:57:30.854738+00:00
-- url     : https://prove2.me/theorems/4cff9378-0171-418e-a170-db7906303b5d
-- title:
--   Lemma 5.7 — isometries U, V : C^{Mτ} → C^T with ∥U†H^kV∥_F ≤ r/q_r² (1 ≤ k < T) and ∥U − V∥_F ≤ √(2r/(1 − r))
-- statement:
--   Fix an input-independent repeated-query circuit with $a$ ancilla qubits, $T$ queries, ancilla gates $V_0,\ldots,V_T$ and query labels $\alpha_t\in[L]$. Its success block $B(P)$ and target $A(P)=\sum_j\lambda_jP_j$ are defined by (1.16)–(1.17). Here $N\ge1$ is one fixed system dimension, $\lambda_j\ge0$, $\sum_j\lambda_j=1$, and $\varepsilon\ge0$. Use the canonical histories from the proof of Lemma 5.2: $W_j=V_{j-1}\cdots V_0$, $\psi_j=W_j^\dagger|0^a\rangle$, $u=W_{T+1}^\dagger|0^a\rangle$, $v=|0^a\rangle$, $\Pi_j=|\psi_j\rangle\langle\psi_j|$, $A_j=I-\Pi_j$. The amplitudes $x_j,y_j,h_{ij}$ are those of (5.4), $H_{ij}=h_{ij}$ for $i>j$ and zero otherwise, and $G$ is their Gram matrix. Assume the uniform error bound (1.17), fix $\tau>\varepsilon$, and put $J_\tau=\{j:\lambda_j\ge\tau\}$, $M_\tau=|J_\tau|$, $r=\varepsilon/\tau$, and $q_r=(\sqrt{4-2r}-\sqrt{2r})/2$. If $N\ge T(M_\tau+1)^2$, there are isometries $U,V:\mathbb C^{M_\tau}\to\mathbb C^T$ such that
--   $$\|U^\dagger H^kV\|_F\le r/q_r^2\quad(1\le k<T),\qquad\|U-V\|_F\le\sqrt{2r/(1-r)}.$$
--   This supplies the isometries used by the ancilla rank bound.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: system dimension N of the input unitaries P_j in U(N) → hypothesis 1 ≤ N; reason: U(0) is the trivial group of empty matrices; N ≥ 1 only excludes the degenerate empty system space
--   - reading: §5 preamble (p.23): λ_j > 0 and ∑_j λ_j = 1; Theorem 5.1: λ_j ≥ 0 → ProbabilityWeights: λ_j ≥ 0 and ∑_j λ_j = 1; reason: the section preamble and Theorem 5.1 disagree on zero weights; the lemmas are read with Theorem 5.1's convention, which contains every positive-weight instance (not the weaker reading)
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 26, Lemma 5.7

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_5_7 {L N : ℕ} (hN : 1 ≤ N) (B : LCUCircuit L)
    (lam : Fin L → ℝ) (hlam : ProbabilityWeights lam) (eps tau : ℝ)
    (heps : 0 ≤ eps) (htau : eps < tau) (happrox : LCUApprox B N lam eps)
    (hdim : B.T*((effectiveSupport lam tau).card+1)^2 ≤ N) :
    ∃ U V : Matrix (Fin B.T) (Fin (effectiveSupport lam tau).card) ℂ,
      IsometryMatrix U ∧ IsometryMatrix V ∧
      (∀ k : ℕ, 1 ≤ k → k < B.T →
        frobenius (U.conjTranspose * historyH B ^ k * V) ≤
          (eps/tau)/(qConstant (eps/tau))^2) ∧
      frobenius (U-V) ≤ Real.sqrt (2*(eps/tau)/(1-eps/tau)) := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
