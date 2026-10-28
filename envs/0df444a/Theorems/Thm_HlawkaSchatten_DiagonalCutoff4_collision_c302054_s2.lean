-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302054_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302054_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:19:07.681165+00:00
-- url     : https://prove2.me/theorems/b1aed665-e1f4-4e56-81d2-8434f2b55dac
-- title:
--   Hlawka collision chart 302055, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[65/16,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302054_s2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((43367/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43367/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44881/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44881/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73149/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-73149/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((75729/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75729/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39817/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39817/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-63459/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-63459/100000 : ℝ)*X 1 2) := by sorry
