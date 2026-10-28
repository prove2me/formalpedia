-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302023_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302023_s1
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T15:16:07.796369+00:00
-- url     : https://prove2.me/theorems/d6195fa9-5e89-4070-9d6e-2efab947f964
-- title:
--   Hlawka collision chart 302024, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[65/16,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302023_s1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4377/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4377/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11767/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(11767/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47881/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(47881/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((73887/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73887/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(35381/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(35381/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83051/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83051/100000 : ℝ)*X 1 2) := by sorry
