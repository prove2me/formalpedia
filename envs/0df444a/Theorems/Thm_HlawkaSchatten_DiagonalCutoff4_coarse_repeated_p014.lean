-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p014
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p014
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:43:24.421318+00:00
-- url     : https://prove2.me/theorems/88b646f4-7e86-43c9-8ee6-169ac6dcf747
-- title:
--   Hlawka repeated-coordinate localization for 23/4 ≤ p ≤ 47/8
-- statement:
--   For every p in [23/4,47/8], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p014 (p : ℝ) (hpa : (23/4 : ℝ) ≤ p) (hpb : p ≤ (47/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (219663/100000 : ℝ) (80409/50000 : ℝ) (82607/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
