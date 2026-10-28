-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304086_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304086_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:37:50.816645+00:00
-- url     : https://prove2.me/theorems/705b4695-ef95-4e41-a30f-62edb5569d62
-- title:
--   Hlawka collision chart 304087, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304086_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((28809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7881/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7881/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15171/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15171/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6527/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6527/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-28011/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-28011/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23613/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23613/50000 : ℝ)*X 1 2) := by sorry
