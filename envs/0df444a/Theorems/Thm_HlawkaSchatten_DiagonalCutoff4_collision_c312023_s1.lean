-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312023_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312023_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:17:24.059891+00:00
-- url     : https://prove2.me/theorems/3e58547e-9e29-44e9-bc37-b721804dcacf
-- title:
--   Hlawka collision chart 312024, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[9/2,37/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312023_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((76149/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76149/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1837/4000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1837/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83759/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83759/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(431/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(431/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13387/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13387/25000 : ℝ)*X 1 2) := by sorry
