-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10059_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10059_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:26:43.083533+00:00
-- url     : https://prove2.me/theorems/66c30b3c-c1b1-482a-b41d-bac907521b7b
-- title:
--   Hlawka collision chart 10060, bounded proof step 7
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10059_s6 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((10657/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10657/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(531/625 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(531/625 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(547/800 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(547/800 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((78249/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78249/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38361/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38361/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(53691/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(53691/100000 : ℝ)*X 1 2) := by sorry
