-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302060_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302060_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:23:46.134854+00:00
-- url     : https://prove2.me/theorems/3372509a-82c9-4096-bb19-67999999f2ed
-- title:
--   Hlawka collision chart 302061, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[65/16,131/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302060_s3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((84979/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84979/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(85723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3831/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3831/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((74657/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74657/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64177/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64177/100000 : ℝ)*X 1 2) := by sorry
