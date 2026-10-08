-- Prove2me | Theorems.Thm_IRLSM_RIP_lemma_6_10
-- name    : IRLSM.RIP.lemma_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:19.436499+00:00
-- url     : https://prove2.me/theorems/702ff92d-28dc-49b4-a767-3803128c9bed
-- title:
--   Lemma 6.10 — ‖X + Z‖_* = ‖X‖_* + ‖Z‖_* when XZ* = 0 and X*Z = 0
-- statement:
--   Let $X$ and $Z$ be real $n\times p$ matrices with $XZ^{\top} = 0$ and $X^{\top}Z = 0$. Then the nuclear norm is additive on them:
--   $$
--   \|X + Z\|_* = \|X\|_* + \|Z\|_* .
--   $$
--
--   This is Lemma 2.3 of Recht, Fazel and Parrilo, recalled in the paper. The two conditions say that the row spaces and the column spaces of $X$ and $Z$ are orthogonal, and the lemma turns orthogonal decompositions into exact nuclear-norm splittings.
--
--   **Formalization Note.** Real matrices, so $X^*$ is $X^{\top}$; $\|\cdot\|_*$ is the sum of the singular values.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Lemma 6.10, p. 19

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- Lemma 6.10 (Lemma 2.3 of Recht–Fazel–Parrilo): if `X Zᵀ = 0` and `Xᵀ Z = 0` then
`‖X + Z‖_* = ‖X‖_* + ‖Z‖_*`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Lemma 6.10, p. 19.

Formalization Note: real matrices, so `X*` is `Xᵀ`; the nuclear norm is the sum of the singular
values (`nuclearNorm` of the published Core module). -/
theorem lemma_6_10 {n p : ℕ} (X Z : Matrix (Fin n) (Fin p) ℝ)
    (h1 : X * Zᵀ = 0) (h2 : Xᵀ * Z = 0) :
    nuclearNorm (X + Z) = nuclearNorm X + nuclearNorm Z := by sorry

end IRLSM.RIP
