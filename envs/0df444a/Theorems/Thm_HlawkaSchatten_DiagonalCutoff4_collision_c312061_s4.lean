-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312061_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312061_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:23:33.623478+00:00
-- url     : https://prove2.me/theorems/742744e6-e372-4db1-ad2f-14102e760b48
-- title:
--   Hlawka collision chart 312062, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312061_s4 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((22839/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22839/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13959/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13959/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6447/25000 : ℝ)*X 1 2)) : False := by sorry
