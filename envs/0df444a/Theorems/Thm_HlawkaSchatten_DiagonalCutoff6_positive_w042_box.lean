-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w042_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w042_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:51:48.282488+00:00
-- url     : https://prove2.me/theorems/0efad3f0-d3ff-4b23-b2bf-a172bb39bb84
-- title:
--   Diagonal Hlawka coordinate box on [55/8, 221/32]
-- statement:
--   Let $p\in[55/8,221/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=268667/100000$, $A=146973/100000$, and $d=8523/10000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(3601/20000)M_i$ for $h\ne i$. Then
--   $$-72533/100000\le X_{ii}\le-29883/50000,\qquad 417/500\le X_{ji}\le 96149/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w042_box (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (221/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (268667/100000 : ℝ) (146973/100000 : ℝ) (8523/10000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3601/20000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(72533/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29883/50000 : ℝ) else (417/500 : ℝ) ≤ X j i ∧ X j i ≤ (96149/100000 : ℝ) := by sorry
