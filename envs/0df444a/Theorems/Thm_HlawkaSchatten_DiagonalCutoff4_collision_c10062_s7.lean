-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10062_s7
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10062_s7
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:29:52.10118+00:00
-- url     : https://prove2.me/theorems/17d81db4-45c1-4d55-b85b-a34be2e0124c
-- title:
--   Hlawka collision chart 10063, bounded proof step 8
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10062_s7 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev6 : (0 : ℝ) ≤ ((17867/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17867/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3593/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3593/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11207/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11207/50000 : ℝ)*X 1 2)) : False := by sorry
