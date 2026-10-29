-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c328062_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c328062_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:01:17.781176+00:00
-- url     : https://prove2.me/theorems/19a3cac5-4971-4d0a-a2e5-ef48a7f0586d
-- title:
--   Hlawka collision chart 328063, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[91/16,93/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c328062_s1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((62083/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62083/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(773/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(773/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1041/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1041/2000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22889/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22889/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22929/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12639/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12639/100000 : ℝ)*X 1 2) := by sorry
