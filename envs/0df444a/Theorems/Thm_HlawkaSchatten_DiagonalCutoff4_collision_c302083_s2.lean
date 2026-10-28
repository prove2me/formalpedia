-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302083_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302083_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:24:12.394992+00:00
-- url     : https://prove2.me/theorems/4be2a977-2a82-472e-8366-3e420b1399bd
-- title:
--   Hlawka collision chart 302084, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[65/16,131/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302083_s2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((66689/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66689/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((8907/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8907/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76309/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76309/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((851/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(851/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((21579/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(21579/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46881/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46881/100000 : ℝ)*X 1 2) := by sorry
