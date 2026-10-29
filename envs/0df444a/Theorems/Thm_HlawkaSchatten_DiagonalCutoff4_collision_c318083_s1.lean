-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318083_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c318083_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:29:30.233347+00:00
-- url     : https://prove2.me/theorems/3cc8987a-9107-48bd-9edc-c523bb154c1f
-- title:
--   Hlawka collision chart 318084, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[39/8,79/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c318083_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((65791/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65791/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((8121/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8121/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(717/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(717/1000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13173/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13173/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((833/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(833/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27943/100000 : ℝ)*X 1 2) := by sorry
