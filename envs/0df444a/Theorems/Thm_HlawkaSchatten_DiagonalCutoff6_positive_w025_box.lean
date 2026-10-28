-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w025_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w025_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:45:47.122761+00:00
-- url     : https://prove2.me/theorems/ccf0affa-1d9d-43cb-a1f3-23634d99a54e
-- title:
--   Diagonal Hlawka coordinate box on [409/64, 205/32]
-- statement:
--   Let $p\in[409/64,205/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=3093/1250$, $A=74931/50000$, and $d=21051/25000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(2143/12500)M_i$ for $h\ne i$. Then
--   $$-17517/25000\le X_{ii}\le-15077/25000,\qquad 10487/12500\le X_{ji}\le 46919/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w025_box (p : ℝ) (hpa : (409/64 : ℝ) ≤ p) (hpb : p ≤ (205/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3093/1250 : ℝ) (74931/50000 : ℝ) (21051/25000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2143/12500 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(17517/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(15077/25000 : ℝ) else (10487/12500 : ℝ) ≤ X j i ∧ X j i ≤ (46919/50000 : ℝ) := by sorry
