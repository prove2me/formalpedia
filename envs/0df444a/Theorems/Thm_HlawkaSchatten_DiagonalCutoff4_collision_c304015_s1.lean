-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304015_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304015_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:27:34.426787+00:00
-- url     : https://prove2.me/theorems/9730d4f8-3f9d-4366-9ae7-fc7e7941a914
-- title:
--   Hlawka collision chart 304016, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[33/8,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304015_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((85129/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85129/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-16137/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-16137/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82389/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82389/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((49243/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49243/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-37161/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-37161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4733/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4733/12500 : ℝ)*X 1 2) := by sorry
