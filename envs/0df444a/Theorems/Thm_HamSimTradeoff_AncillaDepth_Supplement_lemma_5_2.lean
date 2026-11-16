-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_5_2
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:52:58.651043+00:00
-- url     : https://prove2.me/theorems/e1027291-676b-42c8-8a54-385b57e7848e
-- title:
--   Lemma 5.2 — the success block B as an ancilla-compressed product of controlled rank-one-projector gates
-- statement:
--   Fix an input-independent repeated-query circuit with $a$ ancilla qubits, $T$ queries, ancilla gates $V_0,\ldots,V_T$ and query labels $\alpha_t\in[L]$. Its success block $B(P)$ and target $A(P)=\sum_j\lambda_jP_j$ are defined by (1.16)–(1.17). Here $N\ge1$ is one fixed system dimension, $\lambda_j\ge0$, $\sum_j\lambda_j=1$, and $\varepsilon\ge0$. Use the canonical histories from the proof of Lemma 5.2: $W_j=V_{j-1}\cdots V_0$, $\psi_j=W_j^\dagger|0^a\rangle$, $u=W_{T+1}^\dagger|0^a\rangle$, $v=|0^a\rangle$, $\Pi_j=|\psi_j\rangle\langle\psi_j|$, $A_j=I-\Pi_j$. The amplitudes $x_j,y_j,h_{ij}$ are those of (5.4), $H_{ij}=h_{ij}$ for $i>j$ and zero otherwise, and $G$ is their Gram matrix. These particular witnesses are unit vectors, and each $\Pi_j$ is a Hermitian rank-one projector. For every unitary tuple $P\in U(N)^L$,
--   $$B(P)=(\langle u|\otimes I)\prod_{j=T}^{1}(A_j\otimes I+\Pi_j\otimes P_{\alpha_j})(|v\rangle\otimes I).$$
--   This identifies the fixed query circuit with its projector-product representation.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: there exist projector-product witnesses → the explicit witnesses constructed in the proof of Lemma 5.2; reason: fixes the shared objects used in Lemmas 5.5–5.9; no input dependence is introduced
--   - encoding: system dimension N of the input unitaries P_j in U(N) → hypothesis 1 ≤ N; reason: U(0) is the trivial group of empty matrices; N ≥ 1 only excludes the degenerate empty system space
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 24, Lemma 5.2

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_5_2 {L : ℕ} (B : LCUCircuit L) :
    vecNormSq (historyU B) = 1 ∧ vecNormSq (historyV B) = 1 ∧
    (∀ t : Fin B.T, vecNormSq (psi B t) = 1 ∧ (projector B t).rank = 1 ∧
      projector B t * projector B t = projector B t ∧ (projector B t).IsHermitian) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ P : Fin L → Matrix.unitaryGroup (Fin N) ℂ,
      successBlock B (fun j => (P j : Mat N)) =
        (fun i j => ∑ u : Fin (2^B.a), ∑ v : Fin (2^B.a),
          star (historyU B u) *
          (((List.finRange B.T).reverse.map (fun t =>
            Matrix.kronecker (complement B t) (1 : Mat N) +
            Matrix.kronecker (projector B t) (P (B.query t) : Mat N))).prod)
              (u,i) (v,j) * historyV B v) := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
