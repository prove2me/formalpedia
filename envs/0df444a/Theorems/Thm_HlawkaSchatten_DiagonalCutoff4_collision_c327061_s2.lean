-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c327061_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c327061_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:58:37.951579+00:00
-- url     : https://prove2.me/theorems/97b50e4a-0afc-48d8-8870-e4b719a8514e
-- title:
--   Hlawka collision chart 327062, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[89/16,91/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c327061_s2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((26011/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26011/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32543/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1183/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1183/4000 : ℝ)*X 1 2)) : False := by sorry
