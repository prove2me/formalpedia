-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10061_s12
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10061_s12
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:28:50.066983+00:00
-- url     : https://prove2.me/theorems/ed55e372-1b0a-49a1-a01d-3214dc3e4c39
-- title:
--   Hlawka collision chart 10062, bounded proof step 13
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10061_s12 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev11 : (0 : ℝ) ≤ ((12183/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12183/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3563/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3563/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2647/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2647/10000 : ℝ)*X 1 2)) : False := by sorry
