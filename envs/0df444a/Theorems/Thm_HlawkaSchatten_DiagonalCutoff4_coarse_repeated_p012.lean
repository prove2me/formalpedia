-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p012
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p012
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:56:24.655953+00:00
-- url     : https://prove2.me/theorems/a266290f-bca7-4139-af1a-c8cfcb5aec84
-- title:
--   Hlawka repeated coordinate localization for 11/2 ≤ p ≤ 45/8
-- statement:
--   For p in [11/2,45/8], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p012 (p : ℝ) (hpa : (11/2 : ℝ) ≤ p) (hpb : p ≤ (45/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (26117/12500 : ℝ) (8163/5000 : ℝ) (20473/25000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
