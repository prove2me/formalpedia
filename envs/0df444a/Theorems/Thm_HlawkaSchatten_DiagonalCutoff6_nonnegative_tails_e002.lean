-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e002
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e002
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:18:46.441979+00:00
-- url     : https://prove2.me/theorems/8773a52b-6403-4952-828d-62a4624b2d88
-- title:
--   All Hlawka pair tails are nonnegative on [25/4, 51/8]
-- statement:
--   Let $p\in[25/4,51/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=7541/3125$, $A=150819/100000$ and $d=83879/100000$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e002 (p : ℝ) (hpa : (25/4 : ℝ) ≤ p) (hpb : p ≤ (51/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7541/3125 : ℝ) (150819/100000 : ℝ) (83879/100000 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
