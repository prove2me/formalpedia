-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304023_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304023_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:27:49.247475+00:00
-- url     : https://prove2.me/theorems/285e2874-ddf3-4cc1-88c4-24fc7bdaf9d1
-- title:
--   Hlawka collision chart 304024, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[33/8,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304023_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((38237/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38237/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7519/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(7519/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85819/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85819/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7501/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7501/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(881/6250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(881/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33949/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33949/50000 : ℝ)*X 1 2) := by sorry
