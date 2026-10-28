-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304053_s7
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304053_s7
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:32:03.372255+00:00
-- url     : https://prove2.me/theorems/38b6dfa6-573f-4e2c-87e8-e3fa97dc98f7
-- title:
--   Hlawka collision chart 304054, bounded proof step 8
-- statement:
--   For the normalized ordered chart on $[33/8,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304053_s7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev6 : (0 : ℝ) ≤ ((9557/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9557/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43987/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43987/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42537/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42537/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11713/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11713/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27131/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27131/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13137/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13137/50000 : ℝ)*X 1 2) := by sorry
