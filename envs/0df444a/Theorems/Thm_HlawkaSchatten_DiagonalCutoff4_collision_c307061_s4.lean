-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307061_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c307061_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:03:36.422887+00:00
-- url     : https://prove2.me/theorems/ca5917fa-ee7e-44fb-b85a-6176fe59016a
-- title:
--   Hlawka collision chart 307062, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[135/32,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c307061_s4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((3187/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3187/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1351/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1243/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1243/2000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10567/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10567/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48487/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48487/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44079/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44079/100000 : ℝ)*X 1 2) := by sorry
