-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c319062_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c319062_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:34:05.320438+00:00
-- url     : https://prove2.me/theorems/978e896e-5506-46f9-af63-ec4ca37803cd
-- title:
--   Hlawka collision chart 319063, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[79/16,5]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c319062_s2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((43281/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43281/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43661/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43661/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3643/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3643/12500 : ℝ)*X 1 2)) : False := by sorry
