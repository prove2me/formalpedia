-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c326055_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c326055_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:55:34.629504+00:00
-- url     : https://prove2.me/theorems/b7501933-8fc1-497f-8ca8-913e94bf7801
-- title:
--   Hlawka collision chart 326056, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[87/16,89/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c326055_s1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((66743/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66743/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12719/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12719/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64731/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64731/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4481/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4481/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18223/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18223/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7153/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7153/20000 : ℝ)*X 1 2) := by sorry
