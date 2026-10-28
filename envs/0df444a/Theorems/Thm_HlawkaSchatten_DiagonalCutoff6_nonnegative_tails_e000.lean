-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e000
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e000
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:18:45.150306+00:00
-- url     : https://prove2.me/theorems/12e46bf2-c8b0-4993-8eb6-627fb4cfe617
-- title:
--   All Hlawka pair tails are nonnegative on [6, 49/8]
-- statement:
--   Let $p\in[6,49/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=115229/50000$, $A=152691/100000$ and $d=83267/100000$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e000 (p : ℝ) (hpa : (6 : ℝ) ≤ p) (hpb : p ≤ (49/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (115229/50000 : ℝ) (152691/100000 : ℝ) (83267/100000 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
