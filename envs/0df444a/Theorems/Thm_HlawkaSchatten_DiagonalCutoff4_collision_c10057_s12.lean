-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10057_s12
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10057_s12
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:24:13.105775+00:00
-- url     : https://prove2.me/theorems/cf37e7ec-f9e2-46ff-8e25-406871064b2e
-- title:
--   Hlawka collision chart 10058, bounded proof step 13
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10057_s12 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev11 : (0 : ℝ) ≤ ((3799/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3799/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3799/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3799/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(51/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(51/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1407/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1407/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1407/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1407/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(67/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(67/100000 : ℝ)*X 1 2) := by sorry
