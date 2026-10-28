-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301031
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301031
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:23:22.571194+00:00
-- url     : https://prove2.me/theorems/37a24c2b-1a07-4a71-a9b0-a91eb55a31c5
-- title:
--   Hlawka ordered sign chart 291032 excluded
-- statement:
--   For real exponents in $[129/32,65/16]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301031 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by sorry
