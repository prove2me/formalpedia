-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316075_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c316075_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:16:17.6801+00:00
-- url     : https://prove2.me/theorems/783ef4b2-92e5-43fb-8045-bf6c2f3366b7
-- title:
--   Hlawka collision chart 316076, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[19/4,77/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c316075_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((66887/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66887/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-4819/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-4819/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9167/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9167/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12719/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12719/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-27619/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-27619/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9317/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9317/50000 : ℝ)*X 1 2) := by sorry
