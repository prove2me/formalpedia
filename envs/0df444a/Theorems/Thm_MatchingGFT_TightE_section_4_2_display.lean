-- Prove2me | Theorems.Thm_MatchingGFT_TightE_section_4_2_display
-- name    : MatchingGFT.TightE.section_4_2_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:54.543534+00:00
-- url     : https://prove2.me/theorems/50e02e9f-337f-4841-81e8-c7922c99afaa
-- title:
--   §4.2 display — d_L lies strictly between the benchmarks
-- statement:
--   For every $L\ge2$, $p_L^S=p_L^B<d_L<g_L$, where $d_L=(1+1/L)p_L^S$.
--
--   Differences from the source: none.
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), §4.2, display after the definition of d_L, PDF p. 21

import Mathlib
import Definitions.Def_MatchingGFT_TightE_CappedExp

namespace MatchingGFT.TightE

/-- §4.2, the display after the definition of `d_L` (PDF p. 21): for every `L ≥ 2`,
`p_L^S = p_L^B < d_L < g_L`. -/
theorem section_4_2_display (L : ℝ) (hL : 2 ≤ L) :
    cappedPS L = cappedPB L ∧ cappedPB L < cappedD L ∧ cappedD L < cappedG L := by sorry

end MatchingGFT.TightE
