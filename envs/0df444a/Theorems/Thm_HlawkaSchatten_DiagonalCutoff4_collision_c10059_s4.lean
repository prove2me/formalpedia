-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10059_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10059_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:26:43.357749+00:00
-- url     : https://prove2.me/theorems/b69a042c-b405-4658-a3df-391b44905c67
-- title:
--   Hlawka collision chart 10060, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10059_s4 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((46837/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46837/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3761/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3761/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8341/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(8341/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11273/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11273/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90349/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(90349/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(77059/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(77059/100000 : ℝ)*X 1 2) := by sorry
