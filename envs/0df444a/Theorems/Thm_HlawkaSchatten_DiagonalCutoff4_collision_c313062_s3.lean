-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313062_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c313062_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:53:19.729129+00:00
-- url     : https://prove2.me/theorems/c30403ff-6043-420d-8b99-c7dbb44f2412
-- title:
--   Hlawka collision chart 313063, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[73/16,37/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c313062_s3 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((16901/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16901/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34023/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34023/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5307/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5307/25000 : ℝ)*X 1 2)) : False := by sorry
