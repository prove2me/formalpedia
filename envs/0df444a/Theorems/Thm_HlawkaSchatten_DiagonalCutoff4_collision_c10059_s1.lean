-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10059_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10059_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:26:42.024871+00:00
-- url     : https://prove2.me/theorems/3f6ffaf9-8425-4757-8882-e586bc04beaf
-- title:
--   Hlawka collision chart 10060, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10059_s1 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((99087/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(99087/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6207/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6207/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(24109/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(24109/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1957/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1957/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(98197/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(98197/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2317/2500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2317/2500 : ℝ)*X 1 2) := by sorry
