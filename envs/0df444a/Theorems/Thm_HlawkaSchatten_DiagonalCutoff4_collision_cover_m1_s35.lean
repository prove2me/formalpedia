-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_cover_m1_s35
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_cover_m1_s35
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T11:31:39.642087+00:00
-- url     : https://prove2.me/theorems/6f67509e-21ca-4bc8-b5eb-cc964a0f8f97
-- title:
--   Hlawka repeated-coordinate symmetry cover 1, sign pattern 35
-- statement:
--   On the exponent interval $[4,33/8]$, no normalized ordered chart has the displayed signs and dominant-coordinate pattern [0, 0, 1]. All eight orders of the two remaining coordinates are covered. The exact parameters and sign matrix are specified in the formal statement.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_cover_m1_s35 (p : ℝ) (hpa : (4:ℝ) ≤ p) (hpb : p ≤ (33/8:ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X orders ![![true, true, true], ![true, false, false], ![false, true, true]])
    (hm0 : orders 0 0=0) (hm1 : orders 1 0=0) (hm2 : orders 2 0=1) : False := by sorry
