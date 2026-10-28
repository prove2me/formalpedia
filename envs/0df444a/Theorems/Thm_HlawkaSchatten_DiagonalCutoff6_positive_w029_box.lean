-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w029_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w029_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:47:23.571666+00:00
-- url     : https://prove2.me/theorems/c47a32b1-9657-43c8-a2b0-4492a48fffb2
-- title:
--   Diagonal Hlawka coordinate box on [207/32, 13/2]
-- statement:
--   Let $p\in[207/32,13/2]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=62713/25000$, $A=29871/20000$, and $d=84379/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1161/6250)M_i$ for $h\ne i$. Then
--   $$-18011/25000\le X_{ii}\le-29261/50000,\qquad 329/400\le X_{ji}\le 47971/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w029_box (p : ℝ) (hpa : (207/32 : ℝ) ≤ p) (hpb : p ≤ (13/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (62713/25000 : ℝ) (29871/20000 : ℝ) (84379/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1161/6250 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(18011/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29261/50000 : ℝ) else (329/400 : ℝ) ≤ X j i ∧ X j i ≤ (47971/50000 : ℝ) := by sorry
