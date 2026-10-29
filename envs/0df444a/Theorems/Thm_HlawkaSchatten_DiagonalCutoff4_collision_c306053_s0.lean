-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306053_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c306053_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:34:54.004459+00:00
-- url     : https://prove2.me/theorems/64560459-ec01-46fc-8928-9ef79d702f06
-- title:
--   Hlawka collision chart 306054, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[67/16,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c306053_s0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : (0 : ℝ) ≤ ((93047/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(93047/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11843/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11843/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94387/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(94387/100000 : ℝ)*X 1 2) := by sorry
