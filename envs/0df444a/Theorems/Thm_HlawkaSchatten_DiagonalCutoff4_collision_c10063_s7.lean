-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063_s7
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10063_s7
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:31:33.763929+00:00
-- url     : https://prove2.me/theorems/4b1429fc-5485-4c56-8811-3e2a9f07b6ee
-- title:
--   Hlawka collision chart 10064, bounded proof step 8
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10063_s7 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((4327/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4327/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43243/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43243/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83349/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83349/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3337/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3337/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10437/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10437/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1609/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1609/2000 : ℝ)*X 1 2) := by sorry
