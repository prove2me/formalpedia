-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309053_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c309053_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:40:58.247311+00:00
-- url     : https://prove2.me/theorems/0088e658-ba33-4a60-816b-39d720748fc2
-- title:
--   Hlawka collision chart 309054, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[69/16,35/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c309053_s3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((15043/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15043/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27/40 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27/40 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33139/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33139/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1231/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1231/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45597/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45597/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22027/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22027/50000 : ℝ)*X 1 2) := by sorry
