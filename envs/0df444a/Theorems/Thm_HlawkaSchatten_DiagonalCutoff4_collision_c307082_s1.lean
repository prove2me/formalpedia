-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307082_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c307082_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:05:54.711338+00:00
-- url     : https://prove2.me/theorems/fe3c0aae-8178-4f42-b365-23f4249b5e7a
-- title:
--   Hlawka collision chart 307083, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[135/32,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c307082_s1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((82017/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82017/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((46759/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(46759/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(21217/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(21217/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58169/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58169/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((9183/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(9183/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(30363/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(30363/50000 : ℝ)*X 1 2) := by sorry
