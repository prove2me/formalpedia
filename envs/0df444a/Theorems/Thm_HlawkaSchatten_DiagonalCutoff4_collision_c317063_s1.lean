-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317063_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c317063_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:22:27.856093+00:00
-- url     : https://prove2.me/theorems/4e2facc4-8d8e-437b-b815-ab63266799a7
-- title:
--   Hlawka collision chart 317064, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[77/16,39/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c317063_s1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((38387/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38387/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19111/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19111/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18533/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18533/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13987/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13987/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28173/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28173/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53979/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(53979/100000 : ℝ)*X 1 2) := by sorry
