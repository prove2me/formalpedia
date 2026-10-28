-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w063_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w063_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:58:01.644708+00:00
-- url     : https://prove2.me/theorems/a8536c0c-7925-446b-bef1-b5bc56b2939c
-- title:
--   Diagonal Hlawka coordinate box on [63/8, 127/16]
-- statement:
--   Let $p\in[63/8,127/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=312957/100000$, $A=142413/100000$, and $d=86977/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18487/100000)M_i$ for $h\ne i$. Then
--   $$-37993/50000\le X_{ii}\le-1501/2500,\qquad 83589/100000\le X_{ji}\le 24737/25000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w063_box (p : ℝ) (hpa : (63/8 : ℝ) ≤ p) (hpb : p ≤ (127/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (312957/100000 : ℝ) (142413/100000 : ℝ) (86977/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18487/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(37993/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(1501/2500 : ℝ) else (83589/100000 : ℝ) ≤ X j i ∧ X j i ≤ (24737/25000 : ℝ) := by sorry
