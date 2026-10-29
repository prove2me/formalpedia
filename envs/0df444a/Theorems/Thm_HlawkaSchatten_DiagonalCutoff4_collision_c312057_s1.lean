-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312057_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312057_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:22:24.772991+00:00
-- url     : https://prove2.me/theorems/cd12ef5c-1a29-49a6-8ba4-9f55f3a4a6b1
-- title:
--   Hlawka collision chart 312058, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[9/2,73/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312057_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((21309/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21309/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84429/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(84429/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(22521/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(22521/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13121/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13121/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8187/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8187/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13599/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13599/100000 : ℝ)*X 1 2) := by sorry
