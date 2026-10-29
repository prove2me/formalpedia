-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312082_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312082_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:24:21.193418+00:00
-- url     : https://prove2.me/theorems/8343bd3d-bfb4-4930-8f8e-19da807254a2
-- title:
--   Hlawka collision chart 312083, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312082_s0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : (0 : ℝ) ≤ ((73491/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73491/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((21127/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(21127/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(77177/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(77177/100000 : ℝ)*X 1 2) := by sorry
