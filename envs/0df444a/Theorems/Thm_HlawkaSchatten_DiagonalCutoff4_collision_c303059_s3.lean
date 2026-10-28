-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303059_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303059_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:53:40.018923+00:00
-- url     : https://prove2.me/theorems/708eaf8f-0672-41bd-ad42-714769eb7e98
-- title:
--   Hlawka collision chart 303060, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[131/32,33/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303059_s3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((5031/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5031/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39883/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39883/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13483/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13483/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2597/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2597/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16663/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16663/50000 : ℝ)*X 1 2) := by sorry
