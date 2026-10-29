-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312063_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312063_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:23:50.940811+00:00
-- url     : https://prove2.me/theorems/8c3e4a66-d2b5-4f8c-bb98-3af30c8bcbb7
-- title:
--   Hlawka collision chart 312064, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312063_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((34549/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34549/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6919/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6919/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16649/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16649/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6601/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6601/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13417/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13417/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51377/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(51377/100000 : ℝ)*X 1 2) := by sorry
