-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10020
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10020
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:09:10.804182+00:00
-- url     : https://prove2.me/theorems/f6f76e4c-6b12-4d57-9256-b09f990256b7
-- title:
--   Hlawka ordered sign chart 21 excluded
-- statement:
--   For real exponents in $[4,33/8]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10020 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, false]]) : False := by sorry
