-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302054_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c302054_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:19:18.667648+00:00
-- url     : https://prove2.me/theorems/0845be38-b9e8-4971-810f-6285e1a45628
-- title:
--   Hlawka collision chart 302055, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[65/16,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c302054_s3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((75729/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75729/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39817/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39817/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-63459/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-63459/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((62397/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62397/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8199/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8199/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-50523/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-50523/100000 : ℝ)*X 1 2) := by sorry
