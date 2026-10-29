-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312060_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312060_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:22:50.110152+00:00
-- url     : https://prove2.me/theorems/c962b4c5-c8e3-4440-bf7d-ac7097a385ee
-- title:
--   Hlawka collision chart 312061, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312060_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((33167/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33167/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1691/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1691/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-53863/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-53863/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29727/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29727/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33123/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33123/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3923/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3923/20000 : ℝ)*X 1 2) := by sorry
