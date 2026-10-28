-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305061_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c305061_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:57:35.628962+00:00
-- url     : https://prove2.me/theorems/17a6adae-c472-4b86-88f0-13691222f523
-- title:
--   Hlawka collision chart 305062, bounded proof step 7
-- statement:
--   For the normalized ordered chart on $[133/32,67/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c305061_s6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((48549/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48549/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3443/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3443/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24941/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24941/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16979/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16979/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(781/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(781/2500 : ℝ)*X 1 2) := by sorry
