-- Prove2me | Theorems.Thm_LinSysAmp_lemma_4_1
-- name    : LinSysAmp.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:47.638572+00:00
-- url     : https://prove2.me/theorems/2682a413-7782-45e8-bf6f-9db2abc232b2
-- title:
--   Lemma 4.1 — spectrum of the additive walk
-- statement:
--   Let $P$ be the additive walk on $F^{n\times n}$ and $q=|F|$. For every nontrivial additive character $\psi$ of $F$ and every $C\in F^{n\times n}$,
--   $$
--   P\chi_C=q^{-\operatorname{rank}C}\,\chi_C.
--   $$
--   Consequently, $P$ is positive semidefinite and has second eigenvalue at most $1/q$.
--
--   This computes the spectrum of the low-rank walk on all matrices, which the spectral statement about $K_k$ then restricts to $\mathrm{GL}_n(F)$.
--
--   Differences from the source:
--   - generalization: n ≥ 1 (§3.1) → every n : ℕ; reason: n = 0 is a one-point space and the printed case is n ≥ 1
--   - encoding: a fixed nontrivial ψ → every nontrivial ψ for the eigen-relation; the two consequences do not mention ψ; reason: §4.1 fixes an arbitrary ψ, so this is the same claim
--   - encoding: positive semidefinite and second eigenvalue in L²(uniform) → `IsPSDUnif` and `SecondEigLe` of the real kernel; reason: the §3.3 notions; the normalization cancels
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Lemma 4.1, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_LinSysAmp_MarkovNotions
import Definitions.Def_LinSysAmp_additiveWalk

set_option autoImplicit false

open Matrix

namespace LinSysAmp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Lemma 4.1 (Spectrum of the additive walk), p.17 (PDF p.19). Couteau, Melissaris, Radhika Sajith,
arXiv:2611.04680 (version held, sha256 af7a90ac…).

"For every C ∈ F_q^{n×n}, we have Pχ_C = q^{−rank C}χ_C. Consequently, P is positive semidefinite and
has second eigenvalue at most 1/q."

**Formalization Note.** The eigen-relation is stated for every nontrivial additive character
`ψ : F → ℂ` (§4.1 fixes one; the relation holds for each). Positive semidefiniteness and the
second-eigenvalue bound are §3.3's notions (`IsPSDUnif`, `SecondEigLe`) for the real transition kernel
`additiveKernel` with the uniform distribution on `F^{n×n}`; they do not involve `ψ`, so they are
separate conjuncts. `q = Fintype.card F`. -/
theorem lemma_4_1 (n : ℕ) :
    (∀ ψ : AddChar F ℂ, ψ ≠ 1 → ∀ C : Matrix (Fin n) (Fin n) F,
        additiveWalk (chi ψ C) = fun A => ((Fintype.card F : ℂ) ^ C.rank)⁻¹ * chi ψ C A) ∧
      IsPSDUnif (additiveKernel (F := F) (n := n)) ∧
      SecondEigLe (additiveKernel (F := F) (n := n)) (1 / (Fintype.card F : ℝ)) := by sorry

end LinSysAmp
