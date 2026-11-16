-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_5_5
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:55:45.104325+00:00
-- url     : https://prove2.me/theorems/f7b94ad0-8743-404f-be73-fbf64ef7bade
-- title:
--   Lemma 5.5 — the history amplitudes x_j, y_j have squared ℓ² norm at most 1
-- statement:
--   Use the canonical histories from the proof of Lemma 5.2: $W_j=V_{j-1}\cdots V_0$, $\psi_j=W_j^\dagger|0^a\rangle$, $u=W_{T+1}^\dagger|0^a\rangle$, $v=|0^a\rangle$, $\Pi_j=|\psi_j\rangle\langle\psi_j|$, $A_j=I-\Pi_j$. The amplitudes $x_j,y_j,h_{ij}$ are those of (5.4), $H_{ij}=h_{ij}$ for $i>j$ and zero otherwise, and $G$ is their Gram matrix. For every fixed circuit,
--   $$\sum_{j=1}^{T}|x_j|^2\le1,\qquad\sum_{j=1}^{T}|y_j|^2\le1.$$
--   These bounds apply to the actual history amplitudes, including the empty query sequence, and provide their normalization control.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 26, Lemma 5.5

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_5_5 {L : ℕ} (B : LCUCircuit L) :
    (∑ t, ‖historyX B t‖^2) ≤ 1 ∧ (∑ t, ‖historyY B t‖^2) ≤ 1 := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
