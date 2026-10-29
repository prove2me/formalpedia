-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312086_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312086_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:24:43.189699+00:00
-- url     : https://prove2.me/theorems/ea616cd5-e479-4487-8b8a-4ec849e683d4
-- title:
--   Hlawka collision chart 312087, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312086_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((42139/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42139/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-67443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-67443/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63821/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(63821/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((243/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(243/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-9619/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-9619/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15449/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15449/100000 : ℝ)*X 1 2) := by sorry
