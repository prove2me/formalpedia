-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302054
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302054
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:17:48.343249+00:00
-- url     : https://prove2.me/theorems/1e6f8bc3-9ddf-440d-b177-9181d7c2368c
-- title:
--   Hlawka ordered sign chart 292055 excluded
-- statement:
--   For real exponents in $[65/16,33/8]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302054 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by sorry
