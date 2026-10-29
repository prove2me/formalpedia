-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324063_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c324063_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:49:08.943097+00:00
-- url     : https://prove2.me/theorems/bfeaf138-24ed-4c35-8bba-90e594b84c32
-- title:
--   Hlawka collision chart 324064, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[21/4,85/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c324063_s2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((421/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(421/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10707/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10707/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40951/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40951/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6493/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6493/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26329/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26329/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5063/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5063/20000 : ℝ)*X 1 2) := by sorry
