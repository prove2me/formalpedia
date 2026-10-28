-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302052
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302052
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:17:01.432231+00:00
-- url     : https://prove2.me/theorems/c3de6542-2c88-4b7e-bb60-008948e3352d
-- title:
--   Hlawka ordered sign chart 292053 excluded
-- statement:
--   For real exponents in $[65/16,67/16]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302052 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by sorry
