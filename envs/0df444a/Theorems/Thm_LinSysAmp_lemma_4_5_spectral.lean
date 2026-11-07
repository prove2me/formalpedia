-- Prove2me | Theorems.Thm_LinSysAmp_lemma_4_5_spectral
-- name    : LinSysAmp.lemma_4_5_spectral
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:11.336398+00:00
-- url     : https://prove2.me/theorems/eafa9a32-4ff4-42cd-a3d1-63c746d193c6
-- title:
--   Lemma 4.5, item 3 — $K_k$ is reversible, positive semidefinite, with second eigenvalue at most $q^{-k}/(1-e_k)<4q^{-k}$
-- statement:
--   Let $1\le k\le n$ and $q=|F|$. The operator $K_k$ is reversible with respect to the uniform distribution on $\mathrm{GL}_n(F)$, positive semidefinite, and has second eigenvalue at most
--   $$
--   \lambda_k=\frac{q^{-k}}{1-e_k}<4q^{-k}.
--   $$
--
--   A single update of rank $k$ therefore contracts every mean-zero function on $\mathrm{GL}_n(F)$ by a factor exponentially small in $k$. This is the quantitative core of the amplification.
--
--   Differences from the source:
--   - encoding: reversible, positive semidefinite and second eigenvalue in L²(uniform) → `IsReversibleUnif`, `IsPSDUnif` and `SecondEigLe` of the kernel `Kk`; reason: the §3.3 notions; the normalization cancels
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Lemma 4.5, item 3, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_LinSysAmp_MarkovNotions
import Definitions.Def_LinSysAmp_rankUpdate

set_option autoImplicit false

open Matrix

namespace LinSysAmp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Lemma 4.5, item 3, p.19 (PDF p.21). Couteau, Melissaris, Radhika Sajith, arXiv:2611.04680
(version held, sha256 af7a90ac…).

"The operator K_k is reversible with respect to the uniform distribution on GL_n(F_q), positive
semidefinite, and has second eigenvalue at most λ_k = q^{−k}/(1 − e_k) < 4q^{−k}."

**Formalization Note.** `K_k` is the conditioned kernel `Kk n k F` on `InvMat n F` (Definition 4.4);
reversible, PSD and second eigenvalue are §3.3's notions for the uniform distribution
(`IsReversibleUnif`, `IsPSDUnif`, `SecondEigLe`). `q = Fintype.card F`; `q^{−k}` is
`((q : ℝ) ^ k)⁻¹`. The statement has no hypothesis on `e_k`. -/
theorem lemma_4_5_spectral {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsReversibleUnif (Kk n k F) ∧ IsPSDUnif (Kk n k F) ∧
      SecondEigLe (Kk n k F) (((Fintype.card F : ℝ) ^ k)⁻¹ / (1 - ek n k F)) ∧
      ((Fintype.card F : ℝ) ^ k)⁻¹ / (1 - ek n k F) < 4 * ((Fintype.card F : ℝ) ^ k)⁻¹ := by sorry

end LinSysAmp
