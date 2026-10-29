-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317054_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c317054_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:21:37.99923+00:00
-- url     : https://prove2.me/theorems/38e447f3-0d83-41d5-94e8-c21fda2b3743
-- title:
--   Hlawka collision chart 317055, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[77/16,39/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c317054_s2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((1513/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1513/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51443/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38993/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20163/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20163/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1329/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1329/10000 : ℝ)*X 1 2) := by sorry
