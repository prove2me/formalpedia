-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316059_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c316059_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:15:40.645479+00:00
-- url     : https://prove2.me/theorems/517e821e-4910-4d4c-a5d2-52338e3215b6
-- title:
--   Hlawka collision chart 316060, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[19/4,77/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c316059_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((79159/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79159/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39359/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39359/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16151/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16151/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((46387/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46387/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43919/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43919/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(17739/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(17739/100000 : ℝ)*X 1 2) := by sorry
