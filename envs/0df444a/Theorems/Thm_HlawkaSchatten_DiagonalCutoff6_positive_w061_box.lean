-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w061_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w061_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:58:00.016375+00:00
-- url     : https://prove2.me/theorems/58d097ad-6fa1-419b-bf01-b25860dffb63
-- title:
--   Diagonal Hlawka coordinate box on [31/4, 125/16]
-- statement:
--   Let $p\in[31/4,125/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=307391/100000$, $A=35727/25000$, and $d=43391/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(3733/20000)M_i$ for $h\ne i$. Then
--   $$-75861/100000\le X_{ii}\le-373/625,\qquad 83303/100000\le X_{ji}\le 98941/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w061_box (p : ℝ) (hpa : (31/4 : ℝ) ≤ p) (hpb : p ≤ (125/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (307391/100000 : ℝ) (35727/25000 : ℝ) (43391/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3733/20000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(75861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(373/625 : ℝ) else (83303/100000 : ℝ) ≤ X j i ∧ X j i ≤ (98941/100000 : ℝ) := by sorry
