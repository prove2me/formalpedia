-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w057_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w057_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:56:40.279175+00:00
-- url     : https://prove2.me/theorems/6c23ec1d-c804-4ac0-bd8c-0edd579fba64
-- title:
--   Diagonal Hlawka coordinate box on [15/2, 121/16]
-- statement:
--   Let $p\in[15/2,121/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=296283/100000$, $A=8997/6250$, and $d=86373/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(2379/12500)M_i$ for $h\ne i$. Then
--   $$-18903/25000\le X_{ii}\le-2947/5000,\qquad 827/1000\le X_{ji}\le 98927/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w057_box (p : ℝ) (hpa : (15/2 : ℝ) ≤ p) (hpb : p ≤ (121/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (296283/100000 : ℝ) (8997/6250 : ℝ) (86373/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2379/12500 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(18903/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(2947/5000 : ℝ) else (827/1000 : ℝ) ≤ X j i ∧ X j i ≤ (98927/100000 : ℝ) := by sorry
