-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e006
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e006
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:28:59.552423+00:00
-- url     : https://prove2.me/theorems/97143c1d-ae30-4928-ba8a-d5bddfba8303
-- title:
--   All Hlawka pair tails are nonnegative on [27/4, 55/8]
-- statement:
--   Let $p\in[27/4,55/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=263173/100000$, $A=147663/100000$ and $d=42489/50000$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e006 (p : ℝ) (hpa : (27/4 : ℝ) ≤ p) (hpb : p ≤ (55/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (263173/100000 : ℝ) (147663/100000 : ℝ) (42489/50000 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
