-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302018_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302018_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:15:23.230992+00:00
-- url     : https://prove2.me/theorems/1191e5ef-5a6d-4de1-b75e-833f00f67185
-- title:
--   Hlawka collision chart 302019, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[65/16,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302018_s0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]]) : (0 : ℝ) ≤ ((92319/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92319/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(34309/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(34309/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5669/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-5669/6250 : ℝ)*X 1 2) := by sorry
