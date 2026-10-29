-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321063_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c321063_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:40:27.634622+00:00
-- url     : https://prove2.me/theorems/15e116c6-1ca8-4872-9128-0aba41a09fc5
-- title:
--   Hlawka collision chart 321064, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[81/16,41/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c321063_s2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((9537/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9537/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12077/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12077/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11547/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11547/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29457/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28233/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28233/100000 : ℝ)*X 1 2) := by sorry
