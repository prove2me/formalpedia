-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317083_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c317083_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:23:03.109982+00:00
-- url     : https://prove2.me/theorems/f28856f4-f493-47f2-b62e-e0332fd699a4
-- title:
--   Hlawka collision chart 317084, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[77/16,39/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c317083_s2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((14419/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14419/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((14339/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(14339/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15307/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15307/50000 : ℝ)*X 1 2)) : False := by sorry
