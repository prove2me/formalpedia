-- Prove2me | Theorems.Thm_MultiParamQEC_theorem_2_optimal_jnt_qec
-- name    : MultiParamQEC.theorem_2_optimal_jnt_qec
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:44.741684+00:00
-- url     : https://prove2.me/theorems/0d683308-41ac-4ad8-8c35-ee711c3a8ac9
-- title:
--   Theorem 2 (Optimal JNT-QEC) (corrected: $P\cdot\min w\to\min\mathrm{Tr}\,Y$)
-- statement:
--   Let $\mathbb 1_d/\sqrt d,\{G_i\}_{i=1}^P,\{S_i\},\{R_i\}$ be an orthonormal basis of the Hermitian operators on $\mathcal H_S=\mathbb C^d$ with $\mathcal S=\mathrm{span}_{\mathbb R}\{\mathbb 1_d,S_i\}$ (so the multi-parameter HNLS condition holds with $\{G_i\}\subset\mathcal S^\perp$), $P\ge1$, let $W$ be a real positive definite cost matrix and $T>0$ the total time. Then the minimum cost $\Delta^2_W\tilde{\boldsymbol\omega}$ that can be achieved in a JNT-QEC protocol exists and reads
--   $$\Delta^2_W\tilde{\boldsymbol\omega}=\frac1{4T^2}\min_{G^R_i,B_i,\nu_i,K,Y}\mathrm{Tr}\,Y$$
--   subject to
--   $$\mathbb 1_{P+1}\otimes\frac{\mathbb 1_d}{d}+\sum_{i=1}^P(G^R_i)^T\otimes G_i+\sum_i\nu_i\,\mathbb 1_{P+1}\otimes S_i+\sum_iB_i\otimes R_i\ge0,$$
--   $$\Gamma_{ij}=\mathrm{Im}[G^R_j]_{i0},\qquad\begin{pmatrix}Y&K\\K&\mathbb 1_P\end{pmatrix}\ge0,\qquad\begin{pmatrix}K&\mathbb 1_P\\\mathbb 1_P&\Gamma\sqrt{W^{-1}}\end{pmatrix}\ge0,$$
--   where $G^R_i,B_i$ are Hermitian $(P+1)\times(P+1)$ matrices (indices $0,\dots,P$), $\nu_i\in\mathbb R$, and $K,Y$ are real $P\times P$ matrices; the SDP minimum is attained. JNT-QEC protocols use any ancilla, any code space satisfying the QEC condition (6), any input state in it, the evolution (20), any POVM and any estimator locally unbiased at $\boldsymbol\omega=0$.
--
--   The theorem identifies the optimal joint probe, error-correction code and measurement for multi-parameter estimation as the solution of a semidefinite program.
--
--   **Formalization Note** The HNLS hypothesis is the theorem's own "where" clause: the $G_i$ belong to an orthonormal basis whose other members span $\mathcal S$, hence they are orthonormal in $\mathcal S^\perp$.
--
--   Differences from the source:
--   - correction: (8): block [[w 1_P, K], [K, 1_P]] ≥ 0 with w ∈ ℝ and value Δ² = P/(4T²) · min w → block [[Y, K], [K, 1_P]] ≥ 0 with Y a real P × P matrix and value Δ² = 1/(4T²) · min Tr Y; reason: the printed (8) is false for general W: d = 4, P = 2, noiseless (S = span{1}), G₁ = ½σ_z⊗1, G₂ = ½1⊗σ_z, W = diag(1, 100); every feasible point of (8) has w ≥ 400, so (8) gives at least 200/T², while |+⟩|+⟩ with local σ_y measurements and ω̃_k(±) = ±1/T achieves 101/T²; the step 'P min w = min Tr(K²)' on p.9 fails unless K ∝ 1
--   - generalization: S the Lindblad span (5) of the noise → S = span_ℝ{1_d, S_i} for any orthonormal-basis completion, i.e. any real subspace of Hermitian matrices containing 1_d; reason: every Lindblad span (5) is a real subspace of Hermitian matrices containing 1_d, so the statement specializes to the source's
--   - encoding: 1_d/√d, {G_i}, {S_i}, {R_i} an orthonormal basis of the Hermitian operators on H_S → IsOrthonormalHermitianBasis: d² Hermitian matrices, orthonormal for Re Tr(AB); reason: an orthonormal family of d² members of the d²-dimensional real space of Hermitian matrices is a basis
--   - encoding: a POVM {M_ℓ} with outcomes ℓ of unspecified cardinality, sums Σ_ℓ → POVM indexed by ℕ (ObliviousRSP.IsPOVM: PSD elements, HasSum M 1), sums as HasSum, variances summable; reason: every finite or countable POVM is such a family (pad with zero elements); the sums of (2) and (4) must converge for Σ to be defined
--   - encoding: √(W⁻¹) → an argument Rw with Rw.PosSemidef and Rw * Rw = W⁻¹; reason: the positive semidefinite square root is unique, so this is the source's matrix
--   - encoding: reference space H_R = span{|0⟩,…,|P⟩}, indices 0..P; parameter indices 1..P → Fin (P+1) with index 0 the input state; i ∈ 1..P is Fin.succ i for i : Fin P; Q indexed by Fin (P+1) × Fin d, reference first; reason: Lean convention; same instances
--   - encoding: H_S ⊗ H_A with dim H_S = d, H_A an ancilla of any finite dimension → index type Fin d × Fin a (probe first), operators X ⊗ 1 as X ⊗ₖ 1_a, code space given by its orthogonal projection PiC; reason: Lean convention; same instances
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Theorem 2, p.4, display (8) and its "where" clause, p.5

import Mathlib
import Definitions.Def_MultiParamQEC_SDP

open scoped ComplexOrder Matrix Kronecker

namespace MultiParamQEC

/-- **Theorem 2 (Optimal JNT-QEC), corrected** (Górecki–Zhou–Jiang–Demkowicz-Dobrzański,
arXiv:1901.00896v4, Theorem 2, p.4, display (8) and its "where" clause, p.5).

Let `1_d/√d, {G_i}_{i=1}^P, {S_i}, {R_i}` be an orthonormal basis of the Hermitian operators on
`H_S = ℂ^d` with `S = span_ℝ{1_d, S_i}` (so the multi-parameter HNLS condition holds with
`{G_i} ⊂ S^⊥`), let `W` be a real positive definite cost matrix, `√(W⁻¹)` its positive
semidefinite square root (`Rw`), and `T > 0` the total time. Then the minimum of the SDP
`min Tr Y` over Hermitian `G^R_i, B_i` on `ℂ^{P+1}`, `ν_i ∈ ℝ`, and real `P × P` matrices `K, Y`
subject to `Q ≥ 0` (Eq. (25)), `Γ_ij = Im[G^R_j]_{i0}`, `[[Y, K], [K, 1_P]] ≥ 0` and
`[[K, 1_P], [1_P, Γ√(W⁻¹)]] ≥ 0` exists, and the minimum cost `Δ²_W ω̃` achievable by JNT-QEC
(any ancilla, any code space satisfying the QEC condition, any input state in it, any POVM and
any estimator locally unbiased at `ω = 0`) exists and equals `1/(4T²)` times it.

**Formalization Note (correction).** The printed (8) has the scalar block `w 1_P` and the value
`P/(4T²) · min w`; that is false for general `W` (d = 4, P = 2, noiseless, `G₁ = ½σ_z ⊗ 1`,
`G₂ = ½ 1 ⊗ σ_z`, `W = diag(1, 100)`: (8) gives at least `200/T²`, while `|+⟩|+⟩` with local
`σ_y` measurements achieves `101/T²`). The block is replaced by a real matrix `Y` and `P · w` by
`Tr Y`. The HNLS hypothesis is the theorem's own "where" clause: the `G_i` are members of an
orthonormal basis whose other members span `S`, hence orthonormal in `S^⊥`. -/
theorem theorem_2_optimal_jnt_qec {d P m r : ℕ} (hP : 0 < P)
    (G : Fin P → Matrix (Fin d) (Fin d) ℂ) (S : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (R : Fin r → Matrix (Fin d) (Fin d) ℂ) (hbasis : IsOrthonormalHermitianBasis G S R)
    (W : Matrix (Fin P) (Fin P) ℝ) (hW : W.PosDef)
    (Rw : Matrix (Fin P) (Fin P) ℝ) (hRw : Rw.PosSemidef) (hRw2 : Rw * Rw = W⁻¹)
    (T : ℝ) (hT : 0 < T) :
    ∃ v : ℝ, IsLeast (sdpSet G S R Rw) v ∧
      IsLeast (jntCostSet G (noiseSpan S) W T) (v / (4 * T ^ 2)) := by sorry

end MultiParamQEC
