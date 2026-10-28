-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w031_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w031_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:48:09.751206+00:00
-- url     : https://prove2.me/theorems/9e03c3eb-b7d7-4af0-a198-257e4b7d772f
-- title:
--   Diagonal Hlawka coordinate box on [209/32, 105/16]
-- statement:
--   Let $p\in[209/32,105/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=50717/20000$, $A=74481/50000$, and $d=21129/25000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(9243/50000)M_i$ for $h\ne i$. Then
--   $$-72117/100000\le X_{ii}\le-29359/50000,\qquad 41219/50000\le X_{ji}\le 3839/4000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w031_box (p : ℝ) (hpa : (209/32 : ℝ) ≤ p) (hpb : p ≤ (105/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (50717/20000 : ℝ) (74481/50000 : ℝ) (21129/25000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9243/50000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(72117/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29359/50000 : ℝ) else (41219/50000 : ℝ) ≤ X j i ∧ X j i ≤ (3839/4000 : ℝ) := by sorry
