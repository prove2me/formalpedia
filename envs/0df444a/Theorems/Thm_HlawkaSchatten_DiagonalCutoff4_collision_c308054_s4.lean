-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308054_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c308054_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:22:41.074631+00:00
-- url     : https://prove2.me/theorems/534da6c1-f459-4a78-ba70-70af9e3d3cf9
-- title:
--   Hlawka collision chart 308055, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[17/4,69/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c308054_s4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((4239/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4239/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44379/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-30167/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-30167/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6163/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6163/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5171/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5171/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8111/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8111/50000 : ℝ)*X 1 2) := by sorry
