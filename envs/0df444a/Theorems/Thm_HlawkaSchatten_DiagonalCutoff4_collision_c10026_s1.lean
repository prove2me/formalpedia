-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10026_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10026_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:11:03.868861+00:00
-- url     : https://prove2.me/theorems/be28c90a-51ef-4250-8e03-aa54b93968ed
-- title:
--   Hlawka collision chart 10027, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10026_s1 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((23677/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23677/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7019/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(7019/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-37807/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-37807/100000 : ℝ)*X 1 2)) : False := by sorry
