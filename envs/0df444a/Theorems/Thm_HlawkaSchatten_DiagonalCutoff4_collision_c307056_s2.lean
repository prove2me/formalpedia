-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307056_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c307056_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:01:58.23733+00:00
-- url     : https://prove2.me/theorems/04e41ca6-cb8a-4d39-81a9-def1bc476ff3
-- title:
--   Hlawka collision chart 307057, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[135/32,17/4]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c307056_s2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((69267/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69267/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69267/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69267/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-63/1000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-63/1000 : ℝ)*X 1 2)) : False := by sorry
