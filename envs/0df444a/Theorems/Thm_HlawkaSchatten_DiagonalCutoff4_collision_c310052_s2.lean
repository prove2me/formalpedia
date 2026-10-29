-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310052_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310052_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:56:43.880031+00:00
-- url     : https://prove2.me/theorems/0318faf4-42b2-44ab-b464-e1737b5782a4
-- title:
--   Hlawka collision chart 310053, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[35/8,9/2]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310052_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((29171/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29171/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62849/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62849/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10531/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10531/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6009/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6009/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33213/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33213/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-19871/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-19871/100000 : ℝ)*X 1 2) := by sorry
