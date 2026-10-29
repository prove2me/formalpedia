-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p008
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p008
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:36:19.696987+00:00
-- url     : https://prove2.me/theorems/e566c3e4-dd43-4669-8190-015b5b866237
-- title:
--   Hlawka repeated coordinate localization for 5 ≤ p ≤ 41/8
-- statement:
--   For p in [5,41/8], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p008 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
