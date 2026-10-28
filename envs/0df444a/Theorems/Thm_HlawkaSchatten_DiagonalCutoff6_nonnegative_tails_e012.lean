-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e012
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e012
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:38:36.844674+00:00
-- url     : https://prove2.me/theorems/7d06fa7c-31dc-438e-836c-cca33c4be1f0
-- title:
--   All Hlawka pair tails are nonnegative on [15/2, 31/4]
-- statement:
--   Let $p\in[15/2,31/4]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=296283/100000$, $A=8997/6250$ and $d=86373/100000$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e012 (p : ℝ) (hpa : (15/2 : ℝ) ≤ p) (hpb : p ≤ (31/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (296283/100000 : ℝ) (8997/6250 : ℝ) (86373/100000 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
