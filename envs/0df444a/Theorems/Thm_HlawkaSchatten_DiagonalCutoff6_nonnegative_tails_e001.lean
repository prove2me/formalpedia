-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_nonnegative_tails_e001
-- name    : HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e001
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:18:49.953977+00:00
-- url     : https://prove2.me/theorems/028c6b68-4ef4-4e06-ae3d-ebe516540a24
-- title:
--   All Hlawka pair tails are nonnegative on [49/8, 25/4]
-- statement:
--   Let $p\in[49/8,25/4]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=117939/50000$, $A=6069/4000$ and $d=83579/100000$. For each complementary pair $V_i=\sum_{j\ne i}X_j$, all tail coordinates are nonnegative: $$(V_i)_h\ge0\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.nonnegative_tails_e001 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (117939/50000 : ℝ) (6069/4000 : ℝ) (83579/100000 : ℝ) X) :
    ∀ i h, i ≠ h → 0 ≤ pair X i h := by sorry
