-- Prove2me | Theorems.Thm_NisetNoGo_GECC_eq_2
-- name    : NisetNoGo.GECC.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:05.839993+00:00
-- url     : https://prove2.me/theorems/7c35315c-073b-4003-ac35-c4348adafd77
-- title:
--   (2) — complete positivity bounds the noise determinant
-- statement:
--   Let $M,N$ represent a completely positive single-mode Gaussian channel. Then $N$ is positive semidefinite and
--
--   $$\det N\ge(\det M-1)^2.$$
--
--   The determinant bound is the single-mode constraint on channel noise used throughout the paper. Complete positivity is expressed by the covariance matrix inequality in the shared definitions.
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, p. 1, (2)

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

open QAlgorithms.Papers.Independent.Frontier30.P13

namespace NisetNoGo.GECC

theorem eq_2
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (hT : IsCPChannel M N) :
    N.PosSemidef ∧ (M.det - 1) ^ 2 ≤ N.det := by sorry

end NisetNoGo.GECC
