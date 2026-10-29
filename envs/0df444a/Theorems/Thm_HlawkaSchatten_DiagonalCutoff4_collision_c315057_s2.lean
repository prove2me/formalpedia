-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315057_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c315057_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:07:18.538862+00:00
-- url     : https://prove2.me/theorems/021135b2-574d-44ef-8974-d4cf557dc7b0
-- title:
--   Hlawka collision chart 315058, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[75/16,19/4]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c315057_s2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((9623/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9623/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48047/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48047/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(431/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(431/6250 : ℝ)*X 1 2)) : False := by sorry
