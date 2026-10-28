-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e003
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e003
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:18:57.338262+00:00
-- url     : https://prove2.me/theorems/c1e3f38a-d2cf-42fe-b324-b5235577ac13
-- title:
--   All Hlawka pair tails are nonnegative on [51/8, 13/2]
-- statement:
--   Let $p\in[51/8,13/2]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=246759/100000$, $A=37491/25000$ and $d=84169/100000$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e003 (p : ℝ) (hpa : (51/8 : ℝ) ≤ p) (hpb : p ≤ (13/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (246759/100000 : ℝ) (37491/25000 : ℝ) (84169/100000 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
