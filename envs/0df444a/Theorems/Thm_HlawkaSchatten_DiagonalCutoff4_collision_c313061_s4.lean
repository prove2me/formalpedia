-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313061_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c313061_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:53:10.718742+00:00
-- url     : https://prove2.me/theorems/2db14675-0674-46a0-9c70-7c4c14fc13ed
-- title:
--   Hlawka collision chart 313062, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[73/16,37/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c313061_s4 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((4599/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4599/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23283/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23283/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5367/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5367/25000 : ℝ)*X 1 2)) : False := by sorry
