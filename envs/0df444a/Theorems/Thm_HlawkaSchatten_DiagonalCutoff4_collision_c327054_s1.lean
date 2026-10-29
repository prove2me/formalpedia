-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c327054_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c327054_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:58:00.245236+00:00
-- url     : https://prove2.me/theorems/6d603302-3d18-45f7-9252-7f7aea88072b
-- title:
--   Hlawka collision chart 327055, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[89/16,91/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c327054_s1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((30563/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30563/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64409/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64409/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-56769/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-56769/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29411/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29411/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31071/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31071/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-19981/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-19981/100000 : ℝ)*X 1 2) := by sorry
