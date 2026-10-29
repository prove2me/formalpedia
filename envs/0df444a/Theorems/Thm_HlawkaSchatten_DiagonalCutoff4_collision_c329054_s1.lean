-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329054_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c329054_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:03:33.478866+00:00
-- url     : https://prove2.me/theorems/fc85b59b-56dc-4656-a18d-0248c93c6138
-- title:
--   Hlawka collision chart 329055, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[93/16,95/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c329054_s1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((58043/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58043/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61069/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61069/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10763/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10763/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((24273/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24273/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(808/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(808/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-401/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-401/2500 : ℝ)*X 1 2) := by sorry
