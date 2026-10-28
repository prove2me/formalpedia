-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w030_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w030_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:47:31.878646+00:00
-- url     : https://prove2.me/theorems/4ff3b23d-2422-4d0c-8d0c-a25dbdfdce0c
-- title:
--   Diagonal Hlawka coordinate box on [13/2, 209/32]
-- statement:
--   Let $p\in[13/2,209/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=126109/50000$, $A=149157/100000$, and $d=2639/3125$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18531/100000)M_i$ for $h\ne i$. Then
--   $$-72081/100000\le X_{ii}\le-2931/5000,\qquad 10293/12500\le X_{ji}\le 95959/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w030_box (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (209/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (126109/50000 : ℝ) (149157/100000 : ℝ) (2639/3125 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18531/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(72081/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2931/5000 : ℝ) else (10293/12500 : ℝ) ≤ X j i ∧ X j i ≤ (95959/100000 : ℝ) := by sorry
