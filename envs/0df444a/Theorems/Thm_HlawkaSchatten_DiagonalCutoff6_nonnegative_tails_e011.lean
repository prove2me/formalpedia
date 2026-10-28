-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e011
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e011
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:37:21.647803+00:00
-- url     : https://prove2.me/theorems/736d4215-1085-4ccb-bf26-6a8e9873cc9d
-- title:
--   All Hlawka pair tails are nonnegative on [59/8, 15/2]
-- statement:
--   Let $p\in[59/8,15/2]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=145371/50000$, $A=18063/12500$ and $d=43079/50000$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e011 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (145371/50000 : ℝ) (18063/12500 : ℝ) (43079/50000 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
