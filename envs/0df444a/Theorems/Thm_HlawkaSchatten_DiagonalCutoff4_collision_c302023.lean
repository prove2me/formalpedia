-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302023
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302023
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T15:16:03.190963+00:00
-- url     : https://prove2.me/theorems/6eec5bd0-c760-40e4-882c-282aa2934469
-- title:
--   Hlawka ordered sign chart 292024 excluded
-- statement:
--   For real exponents in $[65/16,67/16]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302023 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by sorry
