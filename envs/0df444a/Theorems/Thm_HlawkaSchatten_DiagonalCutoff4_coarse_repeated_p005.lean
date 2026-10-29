-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p005
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p005
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:57:09.079462+00:00
-- url     : https://prove2.me/theorems/8df2dde6-ea5a-4c83-bf0a-6a0c6fb85a58
-- title:
--   Hlawka repeated coordinate localization for 37/8 ≤ p ≤ 19/4
-- statement:
--   For p in [37/8,19/4], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p005 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) :
    ∀ X orders signs, OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
