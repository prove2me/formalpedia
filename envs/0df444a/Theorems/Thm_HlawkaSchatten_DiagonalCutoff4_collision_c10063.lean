-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10063
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10063
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:29:52.078486+00:00
-- url     : https://prove2.me/theorems/4952c2c7-6d38-4ef8-a475-005ad950e9ac
-- title:
--   Hlawka ordered sign chart 64 localized
-- statement:
--   For real exponents in $[4,33/8]$, the normalized ordered chart displayed formally has the three displayed relative bounds for its larger pair tails.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10063 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((9587/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9587/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38787/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38787/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18517/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18517/50000 : ℝ)*X 1 2) := by sorry
