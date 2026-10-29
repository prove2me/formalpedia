-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312059_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312059_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:22:36.910983+00:00
-- url     : https://prove2.me/theorems/2e9d5820-702a-47a9-8cf2-893859d60050
-- title:
--   Hlawka collision chart 312060, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312059_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((85837/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85837/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1069/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1069/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(36891/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(36891/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8583/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8583/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33487/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33487/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(40441/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(40441/100000 : ℝ)*X 1 2) := by sorry
