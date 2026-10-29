-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309061_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309061_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:42:33.973009+00:00
-- url     : https://prove2.me/theorems/5eb1ab85-5a07-499b-ad68-fbde9b9f6e82
-- title:
--   Hlawka collision chart 309062, bounded proof step 7
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309061_s6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((4047/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4047/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20273/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20273/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18811/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18811/100000 : ℝ)*X 1 2)) : False := by sorry
