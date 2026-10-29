-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310075_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310075_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:59:04.813985+00:00
-- url     : https://prove2.me/theorems/5cdb0cf3-fe2e-4149-887e-1c88ad6fa4b1
-- title:
--   Hlawka collision chart 310076, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[35/8,71/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310075_s0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((76421/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76421/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-2731/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2731/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82353/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82353/100000 : ℝ)*X 1 2) := by sorry
