-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311076_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c311076_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:08:17.428255+00:00
-- url     : https://prove2.me/theorems/8345cac0-11cb-4f80-8e51-2ebc09fcc818
-- title:
--   Hlawka collision chart 311077, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[71/16,9/2]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c311076_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((20411/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20411/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-40161/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-40161/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(87209/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(87209/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((39629/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39629/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-2001/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2001/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11371/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11371/25000 : ℝ)*X 1 2) := by sorry
