-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w045_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w045_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:52:52.150429+00:00
-- url     : https://prove2.me/theorems/0beb7bc0-7531-4e30-9be1-de852e87a539
-- title:
--   Diagonal Hlawka coordinate box on [223/32, 7]
-- statement:
--   Let $p\in[223/32,7]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=136397/50000$, $A=5859/4000$, and $d=42707/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17879/100000)M_i$ for $h\ne i$. Then
--   $$-1453/2000\le X_{ii}\le-30021/50000,\qquad 41821/50000\le X_{ji}\le 19239/20000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w045_box (p : ℝ) (hpa : (223/32 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (136397/50000 : ℝ) (5859/4000 : ℝ) (42707/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17879/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(1453/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(30021/50000 : ℝ) else (41821/50000 : ℝ) ≤ X j i ∧ X j i ≤ (19239/20000 : ℝ) := by sorry
