-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303059
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:53:34.110236+00:00
-- url     : https://prove2.me/theorems/783228e0-5273-422e-b69c-3f7eeb5b48af
-- title:
--   Hlawka ordered sign chart 293060 excluded
-- statement:
--   For real exponents in $[131/32,33/8]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303059 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by sorry
