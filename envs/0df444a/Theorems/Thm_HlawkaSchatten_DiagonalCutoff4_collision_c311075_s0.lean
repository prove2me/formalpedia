-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311075_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c311075_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:08:19.775764+00:00
-- url     : https://prove2.me/theorems/1d2ebae8-c64e-49b3-af1d-bec30ddb37c7
-- title:
--   Hlawka collision chart 311076, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[71/16,9/2]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c311075_s0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((74727/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74727/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-85531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-85531/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8081/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8081/10000 : ℝ)*X 1 2) := by sorry
