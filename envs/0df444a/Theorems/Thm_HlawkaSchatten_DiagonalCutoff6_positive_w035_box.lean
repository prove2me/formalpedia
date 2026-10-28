-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w035_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w035_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:49:18.094139+00:00
-- url     : https://prove2.me/theorems/9e5a9ffd-727e-4e18-8e9c-fc41ba922cde
-- title:
--   Diagonal Hlawka coordinate box on [213/32, 107/16]
-- statement:
--   Let $p\in[213/32,107/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=12953/5000$, $A=74103/50000$, and $d=5299/6250$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18307/100000)M_i$ for $h\ne i$. Then
--   $$-14453/20000\le X_{ii}\le-29553/50000,\qquad 41401/50000\le X_{ji}\le 96039/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w035_box (p : ℝ) (hpa : (213/32 : ℝ) ≤ p) (hpb : p ≤ (107/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (12953/5000 : ℝ) (74103/50000 : ℝ) (5299/6250 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18307/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(14453/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29553/50000 : ℝ) else (41401/50000 : ℝ) ≤ X j i ∧ X j i ≤ (96039/100000 : ℝ) := by sorry
