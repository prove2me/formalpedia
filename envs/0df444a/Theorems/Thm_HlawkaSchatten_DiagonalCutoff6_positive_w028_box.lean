-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w028_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w028_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:47:12.768995+00:00
-- url     : https://prove2.me/theorems/137d5380-6204-4ec5-b216-aed1bc1100a5
-- title:
--   Diagonal Hlawka coordinate box on [103/16, 207/32]
-- statement:
--   Let $p\in[103/16,207/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=249487/100000$, $A=149553/100000$, and $d=84309/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18621/100000)M_i$ for $h\ne i$. Then
--   $$-72007/100000\le X_{ii}\le-7303/12500,\qquad 20539/25000\le X_{ji}\le 23981/25000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w028_box (p : ℝ) (hpa : (103/16 : ℝ) ≤ p) (hpb : p ≤ (207/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (249487/100000 : ℝ) (149553/100000 : ℝ) (84309/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18621/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(72007/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7303/12500 : ℝ) else (20539/25000 : ℝ) ≤ X j i ∧ X j i ≤ (23981/25000 : ℝ) := by sorry
