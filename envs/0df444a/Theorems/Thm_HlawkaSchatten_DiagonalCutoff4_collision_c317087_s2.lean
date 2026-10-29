-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317087_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c317087_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:23:11.014954+00:00
-- url     : https://prove2.me/theorems/c6315a54-c00a-41e5-8db3-f9a468e0759d
-- title:
--   Hlawka collision chart 317088, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[77/16,39/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c317087_s2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((49789/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49789/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((49789/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(49789/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49789/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(49789/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29269/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29269/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((29269/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(29269/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29269/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29269/100000 : ℝ)*X 1 2) := by sorry
