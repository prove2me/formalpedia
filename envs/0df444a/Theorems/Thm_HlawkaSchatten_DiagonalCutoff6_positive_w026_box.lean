-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w026_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w026_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:46:31.854778+00:00
-- url     : https://prove2.me/theorems/42c0fc04-e703-4e1b-ba41-403ca030620f
-- title:
--   Diagonal Hlawka coordinate box on [205/32, 411/64]
-- statement:
--   Let $p\in[205/32,411/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=124061/50000$, $A=149757/100000$, and $d=84239/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(137/800)M_i$ for $h\ne i$. Then
--   $$-70091/100000\le X_{ii}\le-30177/50000,\qquad 4197/5000\le X_{ji}\le 23463/25000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w026_box (p : ℝ) (hpa : (205/32 : ℝ) ≤ p) (hpb : p ≤ (411/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (124061/50000 : ℝ) (149757/100000 : ℝ) (84239/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (137/800 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(70091/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(30177/50000 : ℝ) else (4197/5000 : ℝ) ≤ X j i ∧ X j i ≤ (23463/25000 : ℝ) := by sorry
