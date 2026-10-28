-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304027
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304027
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:27:59.042765+00:00
-- url     : https://prove2.me/theorems/860c2c4d-6621-4dec-ad77-ea3032e48b2c
-- title:
--   Hlawka ordered sign chart 294028 excluded
-- statement:
--   For real exponents in $[33/8,17/4]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304027 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by sorry
