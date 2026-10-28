-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T11:40:57.739849+00:00
-- url     : https://prove2.me/theorems/8d20a244-a114-4443-85ad-12d0438d5a21
-- title:
--   Hlawka collision chart 311, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310_s1 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 2, 1], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((23739/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(23739/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((97637/100000 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(97637/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-63913/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-63913/100000 : ℝ)*X 1 1+(-1 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68393/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(68393/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((76121/100000 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(76121/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-3153/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3153/12500 : ℝ)*X 1 1+(-1 : ℝ)*X 1 2) := by sorry
