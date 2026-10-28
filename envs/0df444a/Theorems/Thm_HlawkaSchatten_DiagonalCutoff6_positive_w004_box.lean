-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w004_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w004_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:18:54.754353+00:00
-- url     : https://prove2.me/theorems/c5b323fa-03f0-4d93-8f87-74b5e5530bb2
-- title:
--   Diagonal Hlawka coordinate box on [97/16, 389/64]
-- statement:
--   Let $p\in[97/16,389/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=116583/50000$, $A=76101/50000$, and $d=2607/3125$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17539/100000)M_i$ for $h\ne i$. Then\n$$-69611/100000\le X_{ii}\le-7417/12500,\qquad 5183/6250\le X_{ji}\le 46761/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w004_box (p : ℝ) (hpa : (97/16 : ℝ) ≤ p) (hpb : p ≤ (389/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (116583/50000 : ℝ) (76101/50000 : ℝ) (2607/3125 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17539/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69611/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7417/12500 : ℝ) else (5183/6250 : ℝ) ≤ X j i ∧ X j i ≤ (46761/50000 : ℝ) := by sorry
