-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10075_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10075_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:34:28.002176+00:00
-- url     : https://prove2.me/theorems/efd8dc2c-2f00-43d8-8118-0d3cfcc3c5ca
-- title:
--   Hlawka collision chart 10076, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10075_s3 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((65417/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65417/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-87199/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-87199/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34167/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34167/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1717/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1717/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-64761/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-64761/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(577/1250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(577/1250 : ℝ)*X 1 2) := by sorry
