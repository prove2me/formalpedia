-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311060_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c311060_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:07:32.749421+00:00
-- url     : https://prove2.me/theorems/68a40fca-9278-423b-9115-7ddad33d93b9
-- title:
--   Hlawka collision chart 311061, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[71/16,9/2]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c311060_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((43843/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43843/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2733/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2733/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3979/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3979/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35397/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35397/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2867/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2867/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29459/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29459/50000 : ℝ)*X 1 2) := by sorry
