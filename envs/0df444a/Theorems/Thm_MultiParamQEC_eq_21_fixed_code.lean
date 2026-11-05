-- Prove2me | Theorems.Thm_MultiParamQEC_eq_21_fixed_code
-- name    : MultiParamQEC.eq_21_fixed_code
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:38.275001+00:00
-- url     : https://prove2.me/theorems/2cbe5bf9-2a3c-41f1-aa42-4da61236bcf7
-- title:
--   Eq. (21) — minimum cost for a fixed code space (corrected: frames orthogonal to $|c_0\rangle$)
-- statement:
--   Let $\Pi_C$ be the orthogonal projection onto a code space $\mathcal H_C\subseteq\mathcal H_S\otimes\mathcal H_A$ of dimension at least $2P+1$, $|c_0\rangle=|\psi_{\rm in}\rangle\in\mathcal H_C$ a unit vector, $G_1,\dots,G_P$ Hermitian, $W$ real positive definite and $T>0$. For the JNT-QEC evolution (20), the minimum of $\Delta^2_W\tilde{\boldsymbol\omega}$ over all POVMs on $\mathcal H_S\otimes\mathcal H_A$ and all estimators locally unbiased at $\boldsymbol\omega=0$ equals
--   $$\min_{|c_1\rangle,\dots,|c_P\rangle\in\mathcal H_C}\mathrm{Tr}\big(W(D^TD)^{-1}\big),\qquad D_{ij}=2T\,\mathrm{Im}\langle c_i|(G_j\otimes\mathbb 1_{\dim\mathcal H_A})|c_0\rangle,$$
--   subject to $\langle c_i|c_j\rangle=\delta_{ij}$, $\langle c_i|c_0\rangle=0$ and $D$ invertible; both minima are attained, unless neither program is feasible.
--
--   It reduces the joint optimization over probes and codes to the choice of $P+1$ orthonormal code states $|c_0\rangle,\dots,|c_P\rangle$.
--
--   Differences from the source:
--   - correction: (21): minimum over orthonormal |c_1⟩, …, |c_P⟩ ∈ H_C subject only to ⟨c_i|c_j⟩ = δ_ij → the frame is also required orthogonal to |c_0⟩; reason: the printed (21) is false when ⟨c_0|G_j|c_0⟩ ≠ 0: for P = 1 maximizing |Im⟨c_1|G c_0⟩| over unit c_1 gives ‖G c_0‖, while the optimum is the standard deviation (⟨G²⟩ − ⟨G⟩²)^{1/2}; the c_i come from (19), where they span the x_i ⊥ ψ
--   - encoding: a POVM {M_ℓ} with outcomes ℓ of unspecified cardinality, sums Σ_ℓ → POVM indexed by ℕ (ObliviousRSP.IsPOVM: PSD elements, HasSum M 1), sums as HasSum, variances summable; reason: every finite or countable POVM is such a family (pad with zero elements); the sums of (2) and (4) must converge for Σ to be defined
--   - encoding: H_S ⊗ H_A with dim H_S = d, H_A an ancilla of any finite dimension → index type Fin d × Fin a (probe first), operators X ⊗ 1 as X ⊗ₖ 1_a, code space given by its orthogonal projection PiC; reason: Lean convention; same instances
--   - encoding: (DᵀD)⁻¹ in the objective → D required invertible ((det D) ≠ 0); reason: the inverse is only defined for invertible D; this excludes Mathlib's junk value 0 and no instance of the source
--   - reading: "min" over the cost and over the program, implicitly assuming feasibility → either both sets are empty, or both minima exist and coincide; reason: the stronger reading: no feasibility hypothesis is added, and the degenerate case is stated instead of excluded
--   - generalization: H_C a code subspace satisfying the QEC condition (6) (p.7) → any orthogonal projection PiC of rank at least 2P + 1; reason: (21) follows from (19) applied to the pure-state family (20) inside H_C and does not use (6); every code space of the source is such a projection
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.2, p.7 (dimension requirement) and p.8, Eq. (21)

import Mathlib
import Definitions.Def_MultiParamQEC_JNTQEC

open scoped ComplexOrder Matrix Kronecker

namespace MultiParamQEC

/-- **Minimum cost for a fixed code space** (corrected: frames orthogonal to `c_0`)
(Górecki–Zhou–Jiang–Demkowicz-Dobrzański, arXiv:1901.00896v4, Eq. (21), p.8).

Let `H_C ⊆ H_S ⊗ H_A` be a code space (orthogonal projection `Π_C`) of dimension at least
`2P + 1` ("this space may be required to be at least `2P + 1` dimensional", p.7), `|c_0⟩ = |ψ_in⟩`
a unit vector in `H_C`, `G_j` Hermitian, `W` real positive definite and `T > 0`. Then the minimum
of `Δ²_W ω̃` over all POVMs on `H_S ⊗ H_A` and estimators locally unbiased at `ω = 0`, for the
family (20), equals the minimum of `Tr(W(DᵀD)⁻¹)`, `D_ij = 2T Im⟨c_i|(G_j ⊗ 1)|c_0⟩`, over
orthonormal `c_1, …, c_P ∈ H_C` with `⟨c_i|c_0⟩ = 0` and `D` invertible — unless both programs
are infeasible.

**Formalization Note.** The printed (21) imposes only `⟨c_i|c_j⟩ = δ_ij`; without `⟨c_i|c_0⟩ = 0`
it is false (`P = 1`: maximizing `|Im⟨c_1|G c_0⟩|` over unit `c_1` gives `‖G c_0‖`, whereas the
optimum is the standard deviation `(⟨G²⟩ − ⟨G⟩²)^{1/2}`, smaller when `⟨G⟩ ≠ 0`). The QEC
condition (6) is not used by (21). -/
theorem eq_21_fixed_code {d a P : ℕ} (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (hG : ∀ j, (G j).IsHermitian)
    (PiC : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ) (hPi : IsCodeProjection PiC)
    (hrank : 2 * P + 1 ≤ PiC.rank)
    (ψin : Fin d × Fin a → ℂ) (hψ : star ψin ⬝ᵥ ψin = 1) (hin : PiC *ᵥ ψin = ψin)
    (W : Matrix (Fin P) (Fin P) ℝ) (hW : W.PosDef) (T : ℝ) (hT : 0 < T) :
    (familyCostSet (jntState G PiC ψin T) 0 W = ∅ ∧ codeFrameSet G PiC ψin T W = ∅) ∨
      ∃ v : ℝ, IsLeast (familyCostSet (jntState G PiC ψin T) 0 W) v ∧
        IsLeast (codeFrameSet G PiC ψin T W) v := by sorry

end MultiParamQEC
