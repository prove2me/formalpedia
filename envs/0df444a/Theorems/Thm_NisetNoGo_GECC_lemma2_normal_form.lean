-- Prove2me | Theorems.Thm_NisetNoGo_GECC_lemma2_normal_form
-- name    : NisetNoGo.GECC.lemma2_normal_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:19.581982+00:00
-- url     : https://prove2.me/theorems/f0e191d0-7c05-4493-8165-84142e86bd62
-- title:
--   Lemma 2 proof — local normal forms preserve channel determinants
-- statement:
--   Let $M,N$ represent a completely positive single-mode Gaussian channel. For any two phase shifts and one squeezer, replacing $M$ by $SVMU$ and $N$ by $SVNV^{\mathsf T}S^{\mathsf T}$ gives another completely positive channel and preserves both $\det M$ and $\det N$. Moreover, whenever $\det M>0$, some such transformations make $M=\sqrt{\det M}\,I$; whenever $\det M<0$, some make $M=\sqrt{-\det M}\,\Lambda$, where $\Lambda=\operatorname{diag}(1,-1)$:
--
--   $$\det M'=\det M,\qquad\det N'=\det N.$$
--
--   These are the normal forms used to calculate the asymptotic output entanglement in the two nonsingular determinant regimes.
--
--   **Formalization Note** The statement concerns the covariance matrices and uses the paper's phase shifter and squeezer from (3). It does not assert invariance of logarithmic negativity, which is a separate locality fact.
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, pp. 2–3, proof of Lemma 2, normal-form paragraphs

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

open QAlgorithms.Papers.Independent.Frontier30.P13

namespace NisetNoGo.GECC

theorem lemma2_normal_form
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (hT : IsCPChannel M N) :
    (∀ θ₁ θ₂ s : ℝ,
      (squeezer s * phaseShift θ₂ * M * phaseShift θ₁).det = M.det ∧
      (squeezer s * phaseShift θ₂ * N * (phaseShift θ₂).transpose *
        (squeezer s).transpose).det = N.det ∧
      IsCPChannel (squeezer s * phaseShift θ₂ * M * phaseShift θ₁)
        (squeezer s * phaseShift θ₂ * N * (phaseShift θ₂).transpose *
          (squeezer s).transpose)) ∧
    (0 < M.det → ∃ θ₁ θ₂ s : ℝ,
      squeezer s * phaseShift θ₂ * M * phaseShift θ₁ =
        Real.sqrt M.det • (1 : Matrix (ModeQuadrature (Fin 1))
          (ModeQuadrature (Fin 1)) ℝ)) ∧
    (M.det < 0 → ∃ θ₁ θ₂ s : ℝ,
      squeezer s * phaseShift θ₂ * M * phaseShift θ₁ =
        Real.sqrt (-M.det) • reversal (Fin 1)) := by sorry

end NisetNoGo.GECC
