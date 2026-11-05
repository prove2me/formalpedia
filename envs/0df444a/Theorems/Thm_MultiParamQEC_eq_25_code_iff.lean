-- Prove2me | Theorems.Thm_MultiParamQEC_eq_25_code_iff
-- name    : MultiParamQEC.eq_25_code_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:46.164732+00:00
-- url     : https://prove2.me/theorems/9daa24a8-206a-485b-94d5-1a08ce937c07
-- title:
--   Eqs. (22)–(25) — achievable effective generators are exactly those with a positive code matrix $Q$, ancilla $(P+1)d$ suffices
-- statement:
--   Let $\mathbb 1_d/\sqrt d,\{G_i\}_{i=1}^P,\{S_i\},\{R_i\}$ be an orthonormal basis of the Hermitian operators on $\mathcal H_S=\mathbb C^d$, $P\ge1$, and $\mathcal S=\mathrm{span}_{\mathbb R}\{\mathbb 1_d,S_i\}$. For Hermitian $(P+1)\times(P+1)$ matrices $G^R_1,\dots,G^R_P$:
--
--   1. if for some ancilla dimension $a$ there are orthonormal $|c_0\rangle,\dots,|c_P\rangle\in\mathcal H_S\otimes\mathcal H_A$ whose span satisfies the QEC condition (6) and $[G^R_i]_{kl}=\langle c_k|G_i\otimes\mathbb 1|c_l\rangle$, then there are $\nu_i\in\mathbb R$ and Hermitian $B_i$ such that
--   $$Q=\mathbb 1_{P+1}\otimes\frac{\mathbb 1_d}{d}+\sum_{i}(G^R_i)^T\otimes G_i+\sum_{i}\nu_i\,\mathbb 1_{P+1}\otimes S_i+\sum_{i}B_i\otimes R_i\ge0 ;$$
--   2. conversely, if such $\nu_i$ and $B_i$ exist, such code states exist with ancilla dimension $\dim\mathcal H_A=(P+1)d$.
--
--   This turns the QEC condition on the code states into one semidefinite constraint.
--
--   Differences from the source:
--   - encoding: 1_d/√d, {G_i}, {S_i}, {R_i} an orthonormal basis of the Hermitian operators on H_S → IsOrthonormalHermitianBasis: d² Hermitian matrices, orthonormal for Re Tr(AB); reason: an orthonormal family of d² members of the d²-dimensional real space of Hermitian matrices is a basis
--   - generalization: S the Lindblad span (5) of the noise → S = span_ℝ{1_d, S_i} for any orthonormal-basis completion, i.e. any real subspace of Hermitian matrices containing 1_d; reason: every Lindblad span (5) is a real subspace of Hermitian matrices containing 1_d, so the statement specializes to the source's
--   - encoding: H_S ⊗ H_A with dim H_S = d, H_A an ancilla of any finite dimension → index type Fin d × Fin a (probe first), operators X ⊗ 1 as X ⊗ₖ 1_a, code space given by its orthogonal projection PiC; reason: Lean convention; same instances
--   - encoding: reference space H_R = span{|0⟩,…,|P⟩}, indices 0..P; parameter indices 1..P → Fin (P+1) with index 0 the input state; i ∈ 1..P is Fin.succ i for i : Fin P; Q indexed by Fin (P+1) × Fin d, reference first; reason: Lean convention; same instances
--   - encoding: the code space H_C = span{|c_k⟩}_{k=0}^P → its projection Σ_k |c_k⟩⟨c_k| (codeProj) in the QEC condition; reason: for orthonormal c_k this is the orthogonal projection onto their span; same instances
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.2, p.8, Eqs. (22)–(25) and the paragraph after (25)

import Mathlib
import Definitions.Def_MultiParamQEC_SDP

open scoped ComplexOrder Matrix Kronecker

namespace MultiParamQEC

/-- **QEC codes as one positive semidefinite matrix** (Górecki–Zhou–Jiang–Demkowicz-Dobrzański,
arXiv:1901.00896v4, Eqs. (22)–(25) and the converse, p.8: "`{G^R_i}` is an achievable set of
effective generators in `L(H_R)` (satisfying the QEC condition) if and only if there exist such
`ν_i ∈ ℝ` and `B_i`, for which `Q ≥ 0`", and "It is always sufficient to assume the dimension of
the ancillary space to be `dim H_A = (P + 1)d`").

Let `1_d/√d, G_1, …, G_P, S_1, …, S_m, R_1, …, R_r` be an orthonormal basis of the Hermitian
`d × d` matrices and `S = span_ℝ{1_d, S_i}`. For Hermitian `G^R_1, …, G^R_P` on `ℂ^{P+1}`:
1. if for some ancilla dimension `a` there are orthonormal `c_0, …, c_P ∈ H_S ⊗ H_A` whose span
   satisfies the QEC condition (6) and `[G^R_i]_kl = ⟨c_k|G_i ⊗ 1|c_l⟩`, then there are `ν ∈ ℝ^m`
   and Hermitian `B_i` with `Q ≥ 0` (Eq. (25));
2. conversely, if such `ν` and `B` exist, such `c_0, …, c_P` exist with ancilla dimension
   `a = (P + 1)d`. -/
theorem eq_25_code_iff {d P m r : ℕ} (hP : 0 < P) (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (S : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hbasis : IsOrthonormalHermitianBasis G S R)
    (GR : Fin P → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) (hGR : ∀ i, (GR i).IsHermitian) :
    ((∃ a : ℕ, IsAchievableGenerators G (noiseSpan S) a GR) →
        ∃ (B : Fin r → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) (ν : Fin m → ℝ),
          IsCodeFeasible G S R GR B ν) ∧
      ((∃ (B : Fin r → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) (ν : Fin m → ℝ),
          IsCodeFeasible G S R GR B ν) →
        IsAchievableGenerators G (noiseSpan S) ((P + 1) * d) GR) := by sorry

end MultiParamQEC
