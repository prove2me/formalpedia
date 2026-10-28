-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304054_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304054_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:32:29.830872+00:00
-- url     : https://prove2.me/theorems/6ab82f23-2b5f-4b77-be52-ebfd3e545b57
-- title:
--   Hlawka collision chart 304055, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[33/8,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304054_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((39181/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39181/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82971/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82971/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8387/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8387/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((66089/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66089/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17521/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17521/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2231/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2231/4000 : ℝ)*X 1 2) := by sorry
