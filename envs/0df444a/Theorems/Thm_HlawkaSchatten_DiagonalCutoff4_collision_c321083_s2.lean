-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321083_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c321083_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:40:32.399978+00:00
-- url     : https://prove2.me/theorems/fa31fe54-8df1-4b03-969d-ef186afda19d
-- title:
--   Hlawka collision chart 321084, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[81/16,41/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c321083_s2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((20131/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20131/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((10467/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(10467/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(668/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(668/3125 : ℝ)*X 1 2)) : False := by sorry
