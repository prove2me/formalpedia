-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p006
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p006
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:11:55.261989+00:00
-- url     : https://prove2.me/theorems/47966360-d34d-4a4e-be02-57838d4323ff
-- title:
--   Hlawka repeated coordinate localization for 19/4 ≤ p ≤ 39/8
-- statement:
--   For p in [19/4,39/8], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p006 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
