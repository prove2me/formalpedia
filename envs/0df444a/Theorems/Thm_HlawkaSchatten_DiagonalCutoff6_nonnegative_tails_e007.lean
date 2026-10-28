-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e007
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:31:12.524415+00:00
-- url     : https://prove2.me/theorems/98f5d459-9fa5-4f57-a8ae-eade89ba8a99
-- title:
--   All Hlawka pair tails are nonnegative on [55/8, 7]
-- statement:
--   Let $p\in[55/8,7]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=268667/100000$, $A=146973/100000$ and $d=8523/10000$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e007 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (268667/100000 : ℝ) (146973/100000 : ℝ) (8523/10000 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
