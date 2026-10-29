-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c327053_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c327053_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:58:01.125106+00:00
-- url     : https://prove2.me/theorems/ecd8444f-8733-4b2b-8977-14c816106122
-- title:
--   Hlawka collision chart 327054, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[89/16,91/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c327053_s1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((31447/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31447/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63123/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63123/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61439/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61439/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2373/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29643/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29643/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14241/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14241/50000 : ℝ)*X 1 2) := by sorry
