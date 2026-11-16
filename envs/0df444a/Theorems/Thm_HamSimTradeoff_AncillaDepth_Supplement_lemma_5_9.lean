-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_5_9
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:58:46.270218+00:00
-- url     : https://prove2.me/theorems/b6140d30-8acf-4116-adb1-5f1c8bddd053
-- title:
--   Lemma 5.9 — shift-dilation rank bound: small overlaps ∥U†H^kU∥_F ≤ κ force 2^a ≥ M²/(M + 2κ²(T − 1))
-- statement:
--   Use the canonical histories from the proof of Lemma 5.2: $W_j=V_{j-1}\cdots V_0$, $\psi_j=W_j^\dagger|0^a\rangle$, $u=W_{T+1}^\dagger|0^a\rangle$, $v=|0^a\rangle$, $\Pi_j=|\psi_j\rangle\langle\psi_j|$, $A_j=I-\Pi_j$. The amplitudes $x_j,y_j,h_{ij}$ are those of (5.4), $H_{ij}=h_{ij}$ for $i>j$ and zero otherwise, and $G$ is their Gram matrix. For every real $\kappa\ge0$ and every isometry $U:\mathbb C^M\to\mathbb C^T$, if $\|U^\dagger H^kU\|_F\le\kappa$ for all integers $1\le k<T$, then
--   $$2^a\ge\frac{M^2}{M+2\kappa^2(T-1)}.$$
--   The bound applies to the constructed history matrix, retaining the preceding section's invariants. It turns small shifted overlaps into an ancilla lower bound.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: κ (a bound on Frobenius norms, implicitly nonnegative) → hypothesis 0 ≤ κ; reason: for T ≥ 2 the k = 1 bound forces κ ≥ 0; for T ≤ 1 the hypothesis is vacuous and the conclusion depends on κ² only, so applying the Lean with |κ| gives every instance
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 28, Lemma 5.9

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_5_9 {L M : ℕ} (B : LCUCircuit L) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (U : Matrix (Fin B.T) (Fin M) ℂ) (hU : IsometryMatrix U)
    (hsmall : ∀ k : ℕ, 1 ≤ k → k < B.T →
      frobenius (U.conjTranspose * historyH B ^ k * U) ≤ kappa) :
    (M:ℝ)^2 / ((M:ℝ) + 2*kappa^2*((B.T:ℝ)-1)) ≤ (2:ℝ)^B.a := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
