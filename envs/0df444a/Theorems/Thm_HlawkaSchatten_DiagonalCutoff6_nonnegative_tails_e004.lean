-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e004
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e004
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:18:58.912086+00:00
-- url     : https://prove2.me/theorems/f5aef46e-9b4e-4204-bbb1-c0e83ced1a4c
-- title:
--   All Hlawka pair tails are nonnegative on [13/2, 53/8]
-- statement:
--   Let $p\in[13/2,53/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=126109/50000$, $A=149157/100000$ and $d=2639/3125$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e004 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (126109/50000 : ℝ) (149157/100000 : ℝ) (2639/3125 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
