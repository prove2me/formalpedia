-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w011_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w011_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:37:18.257945+00:00
-- url     : https://prove2.me/theorems/b0384f00-ecc5-4c5d-b916-cf627530fdf6
-- title:
--   Diagonal Hlawka coordinate box on [395/64, 99/16]
-- statement:
--   Let $p\in[395/64,99/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=118957/50000$, $A=7569/5000$, and $d=20923/25000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(3481/20000)M_i$ for $h\ne i$. Then
--   $$-69759/100000\le X_{ii}\le-29833/50000,\qquad 16653/20000\le X_{ji}\le 93629/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w011_box (p : ℝ) (hpa : (395/64 : ℝ) ≤ p) (hpb : p ≤ (99/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (118957/50000 : ℝ) (7569/5000 : ℝ) (20923/25000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3481/20000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69759/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29833/50000 : ℝ) else (16653/20000 : ℝ) ≤ X j i ∧ X j i ≤ (93629/100000 : ℝ) := by sorry
