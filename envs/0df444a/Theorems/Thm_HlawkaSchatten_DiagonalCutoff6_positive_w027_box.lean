-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w027_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w027_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:46:43.685004+00:00
-- url     : https://prove2.me/theorems/bf54bfb1-bf05-43b6-94e5-0ab33eaa5e50
-- title:
--   Diagonal Hlawka coordinate box on [411/64, 103/16]
-- statement:
--   Let $p\in[411/64,103/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=49761/20000$, $A=29931/20000$, and $d=42137/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1069/6250)M_i$ for $h\ne i$. Then
--   $$-7011/10000\le X_{ii}\le-30201/50000,\qquad 16797/20000\le X_{ji}\le 93863/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w027_box (p : ℝ) (hpa : (411/64 : ℝ) ≤ p) (hpb : p ≤ (103/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (49761/20000 : ℝ) (29931/20000 : ℝ) (42137/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(7011/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(30201/50000 : ℝ) else (16797/20000 : ℝ) ≤ X j i ∧ X j i ≤ (93863/100000 : ℝ) := by sorry
