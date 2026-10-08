-- Prove2me | Theorems.Thm_IRLSM_Convergence_lemma_6_10
-- name    : IRLSM.Convergence.lemma_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:56.700488+00:00
-- url     : https://prove2.me/theorems/c764891f-d9e7-400a-b747-f747e2df9d3c
-- title:
--   Lemma 6.10 — $\|X+Z\|_*=\|X\|_*+\|Z\|_*$ when $XZ^*=0$ and $X^*Z=0$
-- statement:
--   Let $X$ and $Z$ be real matrices of the same dimensions. If $XZ^{\mathsf T}=0$ and $X^{\mathsf T}Z=0$, then
--   $$\|X+Z\|_*=\|X\|_*+\|Z\|_*.$$
--
--   The nuclear norm is additive on matrices with mutually orthogonal row and column spaces; this is the step of the inverse triangle inequality (Lemma 6.6) that uses the orthogonality conditions of the SRNSP.
--
--   **Formalization Note** Real matrices, so $XZ^*$ is $XZ^{\mathsf T}$ and $X^*Z$ is $X^{\mathsf T}Z$. The page quotes it as Lemma 2.3 of Recht, Fazel and Parrilo.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Lemma 6.10, p. 19

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Lemma 6.10** (Lemma 2.3 of Recht–Fazel–Parrilo). Let `X` and `Z` be matrices of the same
dimensions. If `X Zᵀ = 0` and `Xᵀ Z = 0`, then `‖X + Z‖_* = ‖X‖_* + ‖Z‖_*`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Lemma 6.10, p. 19.

Formalization Note: real matrices, so `X Z*` is `X * Zᵀ` and `X* Z` is `Xᵀ * Z`. -/
theorem lemma_6_10 {n p : ℕ} (X Z : Matrix (Fin n) (Fin p) ℝ) (h1 : X * Zᵀ = 0)
    (h2 : Xᵀ * Z = 0) : nuclearNorm (X + Z) = nuclearNorm X + nuclearNorm Z := by sorry

end IRLSM.Convergence
