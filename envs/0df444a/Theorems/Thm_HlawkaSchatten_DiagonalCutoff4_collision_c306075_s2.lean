-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306075_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c306075_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:39:25.589975+00:00
-- url     : https://prove2.me/theorems/0a7687da-7803-407c-9935-b9038bb41706
-- title:
--   Hlawka collision chart 306076, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[67/16,135/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c306075_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((59909/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59909/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-81471/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-81471/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6263/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6263/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21517/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21517/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39579/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39579/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26877/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(26877/100000 : ℝ)*X 1 2) := by sorry
