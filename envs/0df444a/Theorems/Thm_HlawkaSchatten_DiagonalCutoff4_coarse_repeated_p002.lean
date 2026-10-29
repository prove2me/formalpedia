-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p002
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p002
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:16:43.552496+00:00
-- url     : https://prove2.me/theorems/8d0657e5-3388-49ea-86e9-7d8ad5a67159
-- title:
--   Hlawka repeated coordinate localization for 17/4 ≤ p ≤ 35/8
-- statement:
--   For p in [17/4,35/8], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p002 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
