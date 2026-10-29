-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p011
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p011
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:53:22.256272+00:00
-- url     : https://prove2.me/theorems/1fff0295-26e1-456b-93d8-41c216cdfb0b
-- title:
--   Hlawka repeated coordinate localization for 43/8 ≤ p ≤ 11/2
-- statement:
--   For p in [43/8,11/2], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p011 (p : ℝ) (hpa : (43/8 : ℝ) ≤ p) (hpb : p ≤ (11/2 : ℝ)) :
    ∀ X orders signs, OrderedChart p (509/250 : ℝ) (82311/50000 : ℝ) (81513/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
