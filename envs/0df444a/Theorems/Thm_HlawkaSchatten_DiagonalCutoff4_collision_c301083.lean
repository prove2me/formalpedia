-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301083
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301083
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:42:56.592843+00:00
-- url     : https://prove2.me/theorems/ab18c154-7881-4c62-adba-5b968025bd41
-- title:
--   Hlawka ordered sign chart 291084 excluded
-- statement:
--   For real exponents in $[129/32,65/16]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301083 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by sorry
