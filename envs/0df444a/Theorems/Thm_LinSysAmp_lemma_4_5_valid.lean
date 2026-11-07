-- Prove2me | Theorems.Thm_LinSysAmp_lemma_4_5_valid
-- name    : LinSysAmp.lemma_4_5_valid
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:24.239207+00:00
-- url     : https://prove2.me/theorems/352a033e-344a-4aca-8cd2-bef7bb2110c8
-- title:
--   Lemma 4.5, item 1 (validity) — an accepted update is invertible, and the masked system has solution $M^{-1}y+z$
-- statement:
--   Let $1\le k\le n$ and let $R$ be a possible non-$\bot$ value of an invertible update of rank $k$, so $R=I_n+UV^\top$ with $\det(I_k+V^\top U)\ne0$. Then $R$ is invertible. Moreover, for every invertible $M$ and all $y,z\in F^n$, the matrix $RM$ is invertible and
--   $$
--   (RM)^{-1}R(y+Mz)=M^{-1}y+z.
--   $$
--
--   This is the fact that makes every query of the algorithm a valid masked copy of the original system, and hence makes a candidate answer checkable against $y$.
--
--   Differences from the source:
--   - encoding: "If R ≠ ⊥" → `some R` lies in the support of the update distribution; reason: the support is exactly the set of non-⊥ outputs
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Lemma 4.5, item 1, first sentence, p.19 (PDF p.21); proof of Proposition 4.8, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_LinSysAmp_rankUpdate

set_option autoImplicit false

open Matrix

namespace LinSysAmp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Lemma 4.5, item 1, first sentence (p.19, PDF p.21), with the solution identity of the proof of
Proposition 4.8 (p.22, PDF p.24). Couteau, Melissaris, Radhika Sajith, arXiv:2611.04680 (version held,
sha256 af7a90ac…).

"If R ≠ ⊥, then R is invertible." and "When R ≠ ⊥, the matrix RM is invertible, and the solution of
the queried system is (RM)⁻¹R(y + Mz) = M⁻¹y + z."

**Formalization Note.** `R ≠ ⊥` is `some R` in the support of the update distribution `updateDist`
(Definition 4.4). Invertibility is `R.det ≠ 0`, and `(RM)⁻¹` is Mathlib's matrix inverse. -/
theorem lemma_4_5_valid {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (R : Matrix (Fin n) (Fin n) F)
    (hR : some R ∈ (updateDist n k F).support) :
    R.det ≠ 0 ∧ ∀ (M : InvMat n F) (y z : Fin n → F),
      (R * M.1).det ≠ 0 ∧ (R * M.1)⁻¹ *ᵥ (R *ᵥ (y + M.1 *ᵥ z)) = M.1⁻¹ *ᵥ y + z := by sorry

end LinSysAmp
