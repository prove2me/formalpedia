-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317059_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c317059_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:22:11.416752+00:00
-- url     : https://prove2.me/theorems/363751f4-816e-4dd0-a3bb-8990def8f858
-- title:
--   Hlawka collision chart 317060, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[77/16,39/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c317059_s1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((77651/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77651/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38607/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38607/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(62623/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(62623/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((40161/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40161/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1527/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1527/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1443/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1443/10000 : ℝ)*X 1 2) := by sorry
