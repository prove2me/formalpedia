-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312075_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312075_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:23:48.094881+00:00
-- url     : https://prove2.me/theorems/a4557091-d238-4a9c-bca4-451410c01b89
-- title:
--   Hlawka collision chart 312076, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312075_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((73077/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73077/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-5233/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-5233/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79281/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31081/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31081/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-6397/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-6397/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36833/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36833/100000 : ℝ)*X 1 2) := by sorry
