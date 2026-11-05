-- Prove2me | Theorems.Thm_MultiParamQEC_eq_26_pre_sdp
-- name    : MultiParamQEC.eq_26_pre_sdp
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:21.607592+00:00
-- url     : https://prove2.me/theorems/c251ba4c-e5d2-49a4-b8fe-9d14630b0d95
-- title:
--   Eq. (26) — the optimal JNT-QEC cost is $\frac1{4T^2}\min\mathrm{Tr}(W(\Gamma^T\Gamma)^{-1})$ subject to $Q\ge0$
-- statement:
--   Let $\mathbb 1_d/\sqrt d,\{G_i\}_{i=1}^P,\{S_i\},\{R_i\}$ be an orthonormal basis of the Hermitian operators on $\mathcal H_S=\mathbb C^d$, $P\ge1$, $\mathcal S=\mathrm{span}_{\mathbb R}\{\mathbb 1_d,S_i\}$, $W$ a real positive definite cost matrix and $T>0$. Then
--   $$\min_{G^R_i,B_i,\nu_i}\mathrm{Tr}\big(W(\Gamma^T\Gamma)^{-1}\big),\qquad\Gamma_{ij}=\mathrm{Im}[G^R_j]_{i0},$$
--   over Hermitian $G^R_i,B_i$ and real $\nu_i$ with $Q\ge0$ (Eq. (25)) exists, and the minimum cost $\Delta^2_W\tilde{\boldsymbol\omega}$ achievable by JNT-QEC protocols (any ancilla, any code satisfying (6), any input state in it, any POVM and any locally unbiased estimator at $\boldsymbol\omega=0$) exists and equals $\frac1{4T^2}$ times it.
--
--   This is the exact, still non-linear, characterization from which the SDP of Theorem 2 is obtained.
--
--   Differences from the source:
--   - encoding: 1_d/√d, {G_i}, {S_i}, {R_i} an orthonormal basis of the Hermitian operators on H_S → IsOrthonormalHermitianBasis: d² Hermitian matrices, orthonormal for Re Tr(AB); reason: an orthonormal family of d² members of the d²-dimensional real space of Hermitian matrices is a basis
--   - generalization: S the Lindblad span (5) of the noise → S = span_ℝ{1_d, S_i} for any orthonormal-basis completion, i.e. any real subspace of Hermitian matrices containing 1_d; reason: every Lindblad span (5) is a real subspace of Hermitian matrices containing 1_d, so the statement specializes to the source's
--   - encoding: a POVM {M_ℓ} with outcomes ℓ of unspecified cardinality, sums Σ_ℓ → POVM indexed by ℕ (ObliviousRSP.IsPOVM: PSD elements, HasSum M 1), sums as HasSum, variances summable; reason: every finite or countable POVM is such a family (pad with zero elements); the sums of (2) and (4) must converge for Σ to be defined
--   - encoding: H_S ⊗ H_A with dim H_S = d, H_A an ancilla of any finite dimension → index type Fin d × Fin a (probe first), operators X ⊗ 1 as X ⊗ₖ 1_a, code space given by its orthogonal projection PiC; reason: Lean convention; same instances
--   - encoding: reference space H_R = span{|0⟩,…,|P⟩}, indices 0..P; parameter indices 1..P → Fin (P+1) with index 0 the input state; i ∈ 1..P is Fin.succ i for i : Fin P; Q indexed by Fin (P+1) × Fin d, reference first; reason: Lean convention; same instances
--   - encoding: (ΓᵀΓ)⁻¹ in the objective → Γ required invertible ((det Γ) ≠ 0); reason: the inverse is only defined for invertible Γ; this excludes Mathlib's junk value 0 and no instance of the source
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.2, p.8, Eq. (26) and the sentence before it

import Mathlib
import Definitions.Def_MultiParamQEC_SDP

open scoped ComplexOrder Matrix Kronecker

namespace MultiParamQEC

/-- **The optimal JNT-QEC cost as the program (26)** (Górecki–Zhou–Jiang–Demkowicz-Dobrzański,
arXiv:1901.00896v4, Eq. (26), p.8).

Let `1_d/√d, G_1, …, G_P, S_1, …, S_m, R_1, …, R_r` be an orthonormal basis of the Hermitian
`d × d` matrices, `S = span_ℝ{1_d, S_i}`, `W` real positive definite and `T > 0`. Then the
minimum of `Tr(W(ΓᵀΓ)⁻¹)`, `Γ_ij = Im[G^R_j]_{i0}`, over Hermitian `G^R_i, B_i` and real `ν_i`
with `Q ≥ 0` (Eq. (25)) exists, and the minimum cost of JNT-QEC exists and equals
`1/(4T²)` times it.

**Formalization Note.** The minimum in (26) runs over feasible points with `Γ` invertible, the
points at which `(ΓᵀΓ)⁻¹` is defined. -/
theorem eq_26_pre_sdp {d P m r : ℕ} (hP : 0 < P) (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (S : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hbasis : IsOrthonormalHermitianBasis G S R)
    (W : Matrix (Fin P) (Fin P) ℝ) (hW : W.PosDef) (T : ℝ) (hT : 0 < T) :
    ∃ v : ℝ, IsLeast (preSdpSet G S R W) v ∧
      IsLeast (jntCostSet G (noiseSpan S) W T) (v / (4 * T ^ 2)) := by sorry

end MultiParamQEC
