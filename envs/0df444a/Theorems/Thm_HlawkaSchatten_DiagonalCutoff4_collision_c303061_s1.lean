-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303061_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303061_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:53:47.999058+00:00
-- url     : https://prove2.me/theorems/c2c6dfd3-dd6d-4137-9d52-ac63cd7750ea
-- title:
--   Hlawka collision chart 303062, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[131/32,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303061_s1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((23949/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23949/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18751/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18751/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94293/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(94293/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5617/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5617/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44079/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44079/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43969/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43969/50000 : ℝ)*X 1 2) := by sorry
