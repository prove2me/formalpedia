-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304063_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304063_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:36:02.860473+00:00
-- url     : https://prove2.me/theorems/d35c37a2-cf36-4976-a681-1e51729ec33c
-- title:
--   Hlawka collision chart 304064, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304063_s5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((36279/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36279/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18253/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18253/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14053/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14053/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31691/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31691/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4017/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4017/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2) := by sorry
