-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312086_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312086_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:24:29.524717+00:00
-- url     : https://prove2.me/theorems/748777eb-5b45-410a-b8c6-60e1d0d3275e
-- title:
--   Hlawka collision chart 312087, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312086_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((75889/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75889/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-42711/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42711/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85183/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85183/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((42139/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42139/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-67443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-67443/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63821/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(63821/100000 : ℝ)*X 1 2) := by sorry
