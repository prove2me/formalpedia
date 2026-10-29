-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318057_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c318057_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:28:31.070619+00:00
-- url     : https://prove2.me/theorems/743007ec-1e04-4771-bbab-fbd7f33102af
-- title:
--   Hlawka collision chart 318058, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[39/8,79/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c318057_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((15111/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15111/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7499/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7499/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(35999/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(35999/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((981/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(981/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7837/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7837/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(979/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(979/50000 : ℝ)*X 1 2) := by sorry
