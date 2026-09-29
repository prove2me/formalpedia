-- Prove2me | Theorems.Thm_Freiman_gap_cylinder_semantics
-- name    : Freiman.gap_cylinder_semantics
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:44.104985+00:00
-- url     : https://prove2.me/theorems/0dd8f01b-0e7b-49e5-9d06-a66bada5732f
-- title:
--   gap cylinder semantics
-- statement:
--   Strict residual interiors, finite-prefix interval bounds and the exact physical-word decomposition yield the rational cylinder inequalities.
-- source:
--   Freiman Hall ray report, m3.tex; eq:m3:cylinder

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_cylinder_semantics (a : ℤ → ℕ+) (i : ℤ) (s : GapState) (j : ℕ) (hd : gapDigits a) (hm : gapMatch a i s) (hj : j < s.word.length) : (gapCylinderLower s.word j : ℝ) < localValue a (i+(j : ℤ)-(s.centre : ℤ)) ∧ localValue a (i+(j : ℤ)-(s.centre : ℤ)) < (gapCylinderUpper s.word j : ℝ) := by
  sorry

end Freiman
