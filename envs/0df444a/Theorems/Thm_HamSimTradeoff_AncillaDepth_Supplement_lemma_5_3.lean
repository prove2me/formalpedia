-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_5_3
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:54:08.948313+00:00
-- url     : https://prove2.me/theorems/42816976-a90a-435e-90c7-64ae3ad43c5d
-- title:
--   Lemma 5.3 — uniform ε-approximation forces every homogeneous component B_r (r ≥ 2) to have norm ≤ ε and B₁ to be ε-close to the target
-- statement:
--   Fix an input-independent repeated-query circuit with $a$ ancilla qubits, $T$ queries, ancilla gates $V_0,\ldots,V_T$ and query labels $\alpha_t\in[L]$. Its success block $B(P)$ and target $A(P)=\sum_j\lambda_jP_j$ are defined by (1.16)–(1.17). Here $N\ge1$ is one fixed system dimension, $\lambda_j\ge0$, $\sum_j\lambda_j=1$, and $\varepsilon\ge0$. Let $B_r(P)$ be the degree-$r$ homogeneous component of the noncommutative expansion (5.6). Suppose $\|B(P)-A(P)\|\le\varepsilon$ for every unitary tuple in this dimension. Then, for every such tuple,
--   $$\|B_r(P)\|\le\varepsilon\quad(r\ge2),\qquad \|B_1(P)-A(P)\|\le\varepsilon.$$
--   The components are computed by summing the circuit's actual query paths, so the statement constrains its nonlinear response.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: system dimension N of the input unitaries P_j in U(N) → hypothesis 1 ≤ N; reason: U(0) is the trivial group of empty matrices; N ≥ 1 only excludes the degenerate empty system space
--   - reading: §5 preamble (p.23): λ_j > 0 and ∑_j λ_j = 1; Theorem 5.1: λ_j ≥ 0 → ProbabilityWeights: λ_j ≥ 0 and ∑_j λ_j = 1; reason: the section preamble and Theorem 5.1 disagree on zero weights; the lemmas are read with Theorem 5.1's convention, which contains every positive-weight instance (not the weaker reading)
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 24, Lemma 5.3

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_5_3 {L N : ℕ} (hN : 1 ≤ N) (B : LCUCircuit L)
    (lam : Fin L → ℝ) (hlam : ProbabilityWeights lam) (eps : ℝ) (heps : 0 ≤ eps)
    (happrox : LCUApprox B N lam eps) :
    ∀ P : Fin L → Matrix.unitaryGroup (Fin N) ℂ,
      (∀ r : ℕ, 2 ≤ r → ‖homogeneous B r (fun j => (P j : Mat N))‖ ≤ eps) ∧
      ‖homogeneous B 1 (fun j => (P j : Mat N)) -
        lcuTarget lam (fun j => (P j : Mat N))‖ ≤ eps := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
