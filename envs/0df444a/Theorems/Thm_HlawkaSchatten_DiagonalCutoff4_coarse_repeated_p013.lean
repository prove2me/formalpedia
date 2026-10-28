-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p013
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p013
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:43:25.448373+00:00
-- url     : https://prove2.me/theorems/9dd6e664-2fb4-4c0c-9b90-631361d44032
-- title:
--   Hlawka repeated-coordinate localization for 45/8 ≤ p ≤ 23/4
-- statement:
--   For every p in [45/8,23/4], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p013 (p : ℝ) (hpa : (45/8 : ℝ) ≤ p) (hpb : p ≤ (23/4 : ℝ)) :
    ∀ X orders signs, OrderedChart p (214291/100000 : ℝ) (80997/50000 : ℝ) (82257/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
