-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318087_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c318087_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:29:31.972916+00:00
-- url     : https://prove2.me/theorems/87ca7090-6dcf-4cf7-95b3-628fb90b4424
-- title:
--   Hlawka collision chart 318088, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[39/8,79/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c318087_s0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((72217/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72217/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((72217/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(72217/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72217/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72217/100000 : ℝ)*X 1 2) := by sorry
