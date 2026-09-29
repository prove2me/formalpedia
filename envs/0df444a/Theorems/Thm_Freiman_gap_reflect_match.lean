-- Prove2me | Theorems.Thm_Freiman_gap_reflect_match
-- name    : Freiman.gap_reflect_match
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:46.570092+00:00
-- url     : https://prove2.me/theorems/29e9133f-07bb-46c0-8d3d-e24ecb699ae5
-- title:
--   gap reflect match
-- statement:
--   Reflecting a marked reversed block restores the same centre at zero.
-- source:
--   Freiman Hall ray report, m3.tex; thm:m3:gap

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_reflect_match (a : ℤ → ℕ+) (s : GapState) (hs : s.centre < s.word.length) (h : gapMatch a 0 (gapReverse s)) : gapMatch (gapReflect a) 0 s := by
  sorry

end Freiman
