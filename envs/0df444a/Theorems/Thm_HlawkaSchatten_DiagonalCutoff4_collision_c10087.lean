-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10087
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10087
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:39:56.073984+00:00
-- url     : https://prove2.me/theorems/ddec4b7a-ef78-43f0-8893-d9c395d32eb3
-- title:
--   Hlawka ordered sign chart 88 localized
-- statement:
--   For real exponents in $[4,33/8]$, the normalized ordered chart displayed formally has the three displayed relative bounds for its larger pair tails.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10087 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((38531/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38531/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((38531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(38531/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38531/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38531/100000 : ℝ)*X 1 2) := by sorry
