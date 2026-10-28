-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304086
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304086
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:37:19.406273+00:00
-- url     : https://prove2.me/theorems/18159e58-c12c-4922-be20-32b85c7f0402
-- title:
--   Hlawka ordered sign chart 294087 excluded
-- statement:
--   For real exponents in $[33/8,133/32]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304086 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by sorry
