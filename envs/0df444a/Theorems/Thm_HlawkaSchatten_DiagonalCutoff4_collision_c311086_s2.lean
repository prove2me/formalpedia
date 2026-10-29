-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c311086_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c311086_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:08:59.350111+00:00
-- url     : https://prove2.me/theorems/c7ce25c3-810c-4a13-98ed-8b65dd65ccef
-- title:
--   Hlawka collision chart 311087, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[71/16,9/2]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c311086_s2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((49129/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49129/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-71403/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-71403/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68943/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6193/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6193/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-8071/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8071/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6421/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6421/25000 : ℝ)*X 1 2) := by sorry
