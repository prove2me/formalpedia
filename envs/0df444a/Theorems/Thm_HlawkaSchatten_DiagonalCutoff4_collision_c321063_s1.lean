-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321063_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c321063_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:40:26.811106+00:00
-- url     : https://prove2.me/theorems/51734512-cb71-4a3b-ba3b-1f4ebc0a3fe7
-- title:
--   Hlawka collision chart 321064, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[81/16,41/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c321063_s1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((71607/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71607/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7137/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7137/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69039/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69039/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9537/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9537/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12077/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12077/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11547/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11547/25000 : ℝ)*X 1 2) := by sorry
