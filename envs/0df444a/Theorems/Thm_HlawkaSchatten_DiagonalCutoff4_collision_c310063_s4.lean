-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310063_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310063_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:59:00.785148+00:00
-- url     : https://prove2.me/theorems/e9d42cea-93a4-49dc-b0be-55c414daff15
-- title:
--   Hlawka collision chart 310064, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[35/8,71/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310063_s4 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((47069/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47069/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47853/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47853/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22861/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22861/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34089/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34089/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17269/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17269/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32999/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32999/100000 : ℝ)*X 1 2) := by sorry
