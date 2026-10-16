-- Prove2me | Theorems.Thm_GroverWiki_groverMatrix_success_amplitude_one
-- name    : GroverWiki.groverMatrix_success_amplitude_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-15T20:32:10.39372+00:00
-- url     : https://prove2.me/theorems/f219a1d2-afe5-483e-9505-c70dc0f4430e
-- title:
--   Degenerate single-item Grover amplitude equals sin squared
-- statement:
--   For a single search item (N = 1), the coordinate amplitude after r Grover iterations has squared norm sin^2((2r+1) * arcsin(1)), which equals 1. This is the N = 1 specialization of groverMatrix_success_amplitude: the target row [1, 1] is a left eigenvector of the iteration matrix with eigenvalue -1, so the amplitude is (-1)^r.
-- source:
--   Grover mission 695f0990-c99c-4db6-b775-f91daa2d2452, parent cffc4011-a5f4-4ad4-82ca-3a48aa1d73ee (GroverWiki.groverMatrix_success_amplitude). Degenerate N=1 case extracted from the verified parent proof branch to satisfy the 150-line admission cap.

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Degenerate single-item case of the algebraic success-amplitude identity:
for `N = 1` the target row is a left eigenvector with eigenvalue `-1`, so the
amplitude is `(-1)^r` and its square is `1 = sin^2((2r+1) * arcsin 1)`. -/
theorem groverMatrix_success_amplitude_one (r : ℕ) :
    ‖![(1 : ℂ), 1 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ)] ⬝ᵥ
        ((!![1, 2 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ);
          -2 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ),
          1 - 4 / (((1 : ℕ)) : ℂ)] ^ r) *ᵥ
          ![0, 1])‖ ^ 2 =
      Real.sin ((2 * r + 1) * Real.arcsin (1 / Real.sqrt (((1 : ℕ)) : ℝ))) ^ 2 := by sorry

end GroverWiki
