-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318086_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c318086_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:29:30.794448+00:00
-- url     : https://prove2.me/theorems/47da908d-4150-4f28-8fa6-3313220abc5c
-- title:
--   Hlawka collision chart 318087, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[39/8,79/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c318086_s2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((727/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(727/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-31099/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-31099/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12339/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12339/50000 : ℝ)*X 1 2)) : False := by sorry
