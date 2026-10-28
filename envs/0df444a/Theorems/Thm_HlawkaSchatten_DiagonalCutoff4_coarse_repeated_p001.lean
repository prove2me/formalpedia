-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p001
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:19:45.259025+00:00
-- url     : https://prove2.me/theorems/347d3fa6-92a4-4bf9-bcf5-6f26b28f7570
-- title:
--   Hlawka repeated coordinate localization for 33/8 ≤ p ≤ 17/4
-- statement:
--   For p in [33/8,17/4], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) :
    ∀ X orders signs, OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
