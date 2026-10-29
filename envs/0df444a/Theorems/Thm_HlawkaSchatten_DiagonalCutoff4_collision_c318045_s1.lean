-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318045_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c318045_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:27:47.567166+00:00
-- url     : https://prove2.me/theorems/c3b88e9f-4eb2-4aa9-8538-bafc3c374538
-- title:
--   Hlawka collision chart 318046, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[39/8,5]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c318045_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((6983/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6983/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-67059/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-67059/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(75753/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63/1250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63/1250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-953/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-953/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20317/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20317/100000 : ℝ)*X 1 2) := by sorry
