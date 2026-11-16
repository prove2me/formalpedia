-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_5_4
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:54:45.032459+00:00
-- url     : https://prove2.me/theorems/8462ffc7-d8af-4675-a297-a6b32fed21e2
-- title:
--   Lemma 5.4 — the endpoint-amplitude matrices C^{(r)} have small principal submatrices in Frobenius norm
-- statement:
--   Fix an input-independent repeated-query circuit with $a$ ancilla qubits, $T$ queries, ancilla gates $V_0,\ldots,V_T$ and query labels $\alpha_t\in[L]$. Its success block $B(P)$ and target $A(P)=\sum_j\lambda_jP_j$ are defined by (1.16)–(1.17). Here $N\ge1$ is one fixed system dimension, $\lambda_j\ge0$, $\sum_j\lambda_j=1$, and $\varepsilon\ge0$. Assume the uniform error bound (1.17). The entry $C^{(r)}_{ji}$ is the sum of all degree-$r$ path amplitudes whose first logical label is $i$ and last logical label is $j$, as in (5.7). For every $S\subseteq[L]$ and $2\le r\le T$ with $N\ge r(|S|+1)^2$,
--   $$\|C^{(r)}_{S,S}\|_F\le\varepsilon.$$
--   Here $\|\cdot\|_F$ is the Frobenius norm. This controls endpoint amplitudes on any selected logical support.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: system dimension N of the input unitaries P_j in U(N) → hypothesis 1 ≤ N; reason: U(0) is the trivial group of empty matrices; N ≥ 1 only excludes the degenerate empty system space
--   - reading: §5 preamble (p.23): λ_j > 0 and ∑_j λ_j = 1; Theorem 5.1: λ_j ≥ 0 → ProbabilityWeights: λ_j ≥ 0 and ∑_j λ_j = 1; reason: the section preamble and Theorem 5.1 disagree on zero weights; the lemmas are read with Theorem 5.1's convention, which contains every positive-weight instance (not the weaker reading)
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 25, Lemma 5.4

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_5_4 {L N : ℕ} (hN : 1 ≤ N) (B : LCUCircuit L)
    (lam : Fin L → ℝ) (hlam : ProbabilityWeights lam) (eps : ℝ) (heps : 0 ≤ eps)
    (happrox : LCUApprox B N lam eps) (S : Finset (Fin L)) (r : ℕ)
    (hr : 2 ≤ r) (hrT : r ≤ B.T) (hdim : r*(S.card+1)^2 ≤ N) :
    principalFrobenius (endpointMatrix B r) S ≤ eps := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
