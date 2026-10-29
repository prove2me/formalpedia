-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315059_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c315059_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:07:23.182516+00:00
-- url     : https://prove2.me/theorems/0b4417b5-b3a9-4f20-b866-1c03eae2c1e9
-- title:
--   Hlawka collision chart 315060, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[75/16,19/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c315059_s0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : (0 : ℝ) ≤ ((10091/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10091/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10037/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10037/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(66697/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(66697/100000 : ℝ)*X 1 2) := by sorry
