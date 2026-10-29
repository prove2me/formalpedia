-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c325062_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c325062_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:52:22.97799+00:00
-- url     : https://prove2.me/theorems/e39d22b3-b073-4fcb-932d-14edf943e64f
-- title:
--   Hlawka collision chart 325063, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[85/16,87/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c325062_s0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : (0 : ℝ) ≤ ((2711/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2711/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(337/500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(337/500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-57143/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-57143/100000 : ℝ)*X 1 2) := by sorry
