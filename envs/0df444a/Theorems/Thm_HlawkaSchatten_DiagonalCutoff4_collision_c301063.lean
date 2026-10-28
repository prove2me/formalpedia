-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301063
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301063
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:39:18.146983+00:00
-- url     : https://prove2.me/theorems/9820a464-8e28-4c3c-913e-4d427489ea3a
-- title:
--   Hlawka ordered sign chart 291064 localized
-- statement:
--   For real exponents in $[129/32,65/16]$, the normalized ordered chart displayed formally has the three displayed relative bounds for its larger pair tails.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301063 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((3839/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3839/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31007/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14821/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14821/50000 : ℝ)*X 1 2) := by sorry
