-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w037_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w037_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:49:53.797372+00:00
-- url     : https://prove2.me/theorems/94d1a266-a549-428a-b111-ed00aba0c469
-- title:
--   Diagonal Hlawka coordinate box on [215/32, 27/4]
-- statement:
--   Let $p\in[215/32,27/4]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=261801/100000$, $A=147843/100000$, and $d=42457/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18221/100000)M_i$ for $h\ne i$. Then
--   $$-36171/50000\le X_{ii}\le-1853/3125,\qquad 2593/3125\le X_{ji}\le 12009/12500\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w037_box (p : ℝ) (hpa : (215/32 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (261801/100000 : ℝ) (147843/100000 : ℝ) (42457/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18221/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(36171/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(1853/3125 : ℝ) else (2593/3125 : ℝ) ≤ X j i ∧ X j i ≤ (12009/12500 : ℝ) := by sorry
