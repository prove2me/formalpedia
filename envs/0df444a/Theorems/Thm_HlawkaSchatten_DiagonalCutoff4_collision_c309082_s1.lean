-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309082_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309082_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:43:31.406989+00:00
-- url     : https://prove2.me/theorems/360d7b1a-aaa6-433c-bea4-324fd5398d88
-- title:
--   Hlawka collision chart 309083, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309082_s1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((15869/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15869/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((90717/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(90717/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(82647/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(82647/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9443/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9443/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((61141/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(61141/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(24957/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(24957/50000 : ℝ)*X 1 2) := by sorry
