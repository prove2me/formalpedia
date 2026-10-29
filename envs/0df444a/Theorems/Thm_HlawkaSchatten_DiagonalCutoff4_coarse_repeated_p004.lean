-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p004
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p004
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:14:41.477816+00:00
-- url     : https://prove2.me/theorems/180ff107-5db5-4512-9f34-9eb5e592aff6
-- title:
--   Hlawka repeated coordinate localization for 9/2 ≤ p ≤ 37/8
-- statement:
--   For p in [9/2,37/8], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p004 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
