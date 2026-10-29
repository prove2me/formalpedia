-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312051_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312051_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:19:11.240981+00:00
-- url     : https://prove2.me/theorems/9d362ec4-3613-435d-a074-cd5b98ca7a44
-- title:
--   Hlawka collision chart 312052, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[9/2,37/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312051_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((78949/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78949/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78167/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(39683/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(39683/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44003/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44003/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10981/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10981/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4783/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4783/50000 : ℝ)*X 1 2) := by sorry
