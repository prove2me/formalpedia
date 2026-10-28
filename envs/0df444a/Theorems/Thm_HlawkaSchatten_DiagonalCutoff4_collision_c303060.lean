-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303060
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303060
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:53:40.186351+00:00
-- url     : https://prove2.me/theorems/17a06e3f-6216-44d2-8819-676460a57fc5
-- title:
--   Hlawka ordered sign chart 293061 excluded
-- statement:
--   For real exponents in $[131/32,33/8]$, the normalized ordered chart displayed formally is impossible.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303060 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : False := by sorry
