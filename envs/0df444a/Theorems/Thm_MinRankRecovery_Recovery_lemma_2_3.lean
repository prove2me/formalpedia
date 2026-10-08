-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_lemma_2_3
-- name    : MinRankRecovery.Recovery.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:27.958627+00:00
-- url     : https://prove2.me/theorems/239ff7c5-dee7-48ee-b248-9e617b6b2db2
-- title:
--   Lemma 2.3 — AB′ = 0 and A′B = 0 imply ‖A + B‖_* = ‖A‖_* + ‖B‖_*
-- statement:
--   Let $M$ and $N$ be real $m\times n$ matrices and let $\|\cdot\|_*$ denote the nuclear norm (the sum of the singular values). If
--   $$MN^{\top}=0\qquad\text{and}\qquad M^{\top}N=0,$$
--   then
--   $$\|M+N\|_*=\|M\|_*+\|N\|_*.$$
--
--   The two conditions say that $M$ and $N$ have orthogonal row spaces and orthogonal column spaces. The lemma is the matrix analogue of the additivity of the $\ell_1$ norm on vectors with disjoint supports, and it is the step of the proof of Theorem 3.3 that turns the triangle inequality into the cone condition (3.4).
--
--   **Formalization Note** The paper names the two matrices $A$ and $B$; here they are $M$ and $N$, because $\mathcal A$ denotes the linear map elsewhere in the mission. $AB'$ is `M * Nᵀ` and $A'B$ is `Mᵀ * N`.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Lemma 2.3, p. 9

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- Lemma 2.3, p. 9: if `M Nᵀ = 0` and `Mᵀ N = 0` then `‖M + N‖_* = ‖M‖_* + ‖N‖_*`. -/
theorem lemma_2_3 {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℝ) (h1 : M * Nᵀ = 0)
    (h2 : Mᵀ * N = 0) :
    nuclearNorm (M + N) = nuclearNorm M + nuclearNorm N := by sorry

end MinRankRecovery.Recovery
