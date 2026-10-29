-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315055_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c315055_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:07:09.926789+00:00
-- url     : https://prove2.me/theorems/f22e5739-e406-4a57-8863-36db6c5251a5
-- title:
--   Hlawka collision chart 315056, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[75/16,19/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c315055_s2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((29969/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29969/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5887/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5887/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29829/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35791/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35791/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2291/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2291/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36199/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36199/100000 : ℝ)*X 1 2) := by sorry
