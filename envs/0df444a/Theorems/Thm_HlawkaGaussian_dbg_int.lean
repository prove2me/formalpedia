-- Prove2me | Theorems.Thm_HlawkaGaussian_dbg_int
-- name    : HlawkaGaussian.dbg_int
-- status  : Open
-- author  : @sorry_not_sorry
-- created : 2026-10-08T06:29:38.372356+00:00
-- url     : https://prove2.me/theorems/feed3bd0-fa7b-47ce-b046-778eb4a75daa
-- title:
--   diag
-- statement:
--   diagnostic
-- source:
--   diag

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HlawkaGaussian.dbg_int : ∫ (t : ℝ), t ∂(ProbabilityTheory.gaussianReal 0 1) = 0 := by sorry
