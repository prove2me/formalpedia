-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_5_8
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:58:10.463915+00:00
-- url     : https://prove2.me/theorems/37bcea4d-b973-4212-9e38-74180faaeef9
-- title:
--   Lemma 5.8 — Gram-matrix identity G = (I − H)^{−†}(I − H†H)(I − H)^{−1}; hence I − H†H ⪰ 0, ∥H∥ ≤ 1, rank(I − H†H) ≤ 2^a
-- statement:
--   Use the canonical histories from the proof of Lemma 5.2: $W_j=V_{j-1}\cdots V_0$, $\psi_j=W_j^\dagger|0^a\rangle$, $u=W_{T+1}^\dagger|0^a\rangle$, $v=|0^a\rangle$, $\Pi_j=|\psi_j\rangle\langle\psi_j|$, $A_j=I-\Pi_j$. The amplitudes $x_j,y_j,h_{ij}$ are those of (5.4), $H_{ij}=h_{ij}$ for $i>j$ and zero otherwise, and $G$ is their Gram matrix. For every circuit's specific history matrices,
--   $$G=((I-H)^{-1})^\dagger(I-H^\dagger H)(I-H)^{-1}.$$
--   Consequently,
--   $$I-H^\dagger H\succeq0,\qquad\|H\|\le1,\qquad\operatorname{rank}(I-H^\dagger H)=\operatorname{rank}(G)\le2^a.$$
--   Positive semidefiniteness is expressed as nonnegativity of the real quadratic form on every vector. The matrix is Hermitian by its formula. This connects the history geometry to available ancilla dimension.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: I-H†H is positive semidefinite → every real quadratic form is nonnegative; reason: the displayed matrix is Hermitian identically, so this is exactly complex positive semidefiniteness
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 27, Lemma 5.8

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_5_8 {L : ℕ} (B : LCUCircuit L) :
    gram B = ((1-historyH B)⁻¹).conjTranspose *
      (1-(historyH B).conjTranspose*historyH B) * (1-historyH B)⁻¹ ∧
    (∀ v : Fin B.T → ℂ,
      0 ≤ (braKet v ((1-(historyH B).conjTranspose*historyH B).mulVec v)).re) ∧
    ‖historyH B‖ ≤ 1 ∧
    (1-(historyH B).conjTranspose*historyH B).rank = (gram B).rank ∧
    (gram B).rank ≤ 2^B.a := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
