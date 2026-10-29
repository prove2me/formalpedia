-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c325061_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c325061_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:52:18.139757+00:00
-- url     : https://prove2.me/theorems/d4ee8c96-d33b-4713-9b30-3f22494afcf7
-- title:
--   Hlawka collision chart 325062, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[85/16,87/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c325061_s1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((68417/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68417/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67693/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67693/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31423/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31423/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6523/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6523/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39307/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39307/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35437/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35437/100000 : ℝ)*X 1 2) := by sorry
