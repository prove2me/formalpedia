-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314045_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c314045_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:59:34.726199+00:00
-- url     : https://prove2.me/theorems/26734f26-49ae-4867-adff-0411143af3fb
-- title:
--   Hlawka collision chart 314046, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[37/8,19/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c314045_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((65707/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65707/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-36229/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-36229/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81741/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(81741/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3773/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3773/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35213/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-35213/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4869/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4869/12500 : ℝ)*X 1 2) := by sorry
