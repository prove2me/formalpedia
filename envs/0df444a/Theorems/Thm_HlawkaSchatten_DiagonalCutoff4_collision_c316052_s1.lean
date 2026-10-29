-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316052_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c316052_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:14:23.684932+00:00
-- url     : https://prove2.me/theorems/89aa2740-0d3d-410b-931b-c0c7f6b78923
-- title:
--   Hlawka collision chart 316053, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[19/4,39/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c316052_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((9141/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9141/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37107/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37107/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-249/400 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-249/400 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((37363/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37363/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2079/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2079/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-321/1250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-321/1250 : ℝ)*X 1 2) := by sorry
