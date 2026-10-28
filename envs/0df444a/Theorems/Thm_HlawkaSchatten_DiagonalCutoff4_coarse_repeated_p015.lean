-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p015
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p015
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:43:54.076868+00:00
-- url     : https://prove2.me/theorems/925e2d4b-174e-4117-bf52-17d8b52583c0
-- title:
--   Hlawka repeated-coordinate localization for 47/8 ≤ p ≤ 6
-- statement:
--   For every p in [47/8,6], the displayed normalized parameters force distinct dominant pair coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p015 (p : ℝ) (hpa : (47/8 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) :
    ∀ X orders signs, OrderedChart p (225053/100000 : ℝ) (159717/100000 : ℝ) (82943/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by sorry
