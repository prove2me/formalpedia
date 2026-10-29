-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313056_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c313056_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:52:12.230681+00:00
-- url     : https://prove2.me/theorems/886650b9-9a14-4a1f-af38-f78b6bf2101f
-- title:
--   Hlawka collision chart 313057, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[73/16,37/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c313056_s0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]]) : (0 : ℝ) ≤ ((15679/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15679/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15679/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15679/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-3153/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-3153/12500 : ℝ)*X 1 2) := by sorry
