-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304087
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304087
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:38:10.692211+00:00
-- url     : https://prove2.me/theorems/e9e9091f-b980-4123-a883-173515a5262e
-- title:
--   Hlawka ordered sign chart 294088 localized
-- statement:
--   For real exponents in $[33/8,133/32]$, the normalized ordered chart displayed formally has the three displayed relative bounds for its larger pair tails.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304087 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((16803/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16803/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((16803/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(16803/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16803/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16803/50000 : ℝ)*X 1 2) := by sorry
