-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w019_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w019_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:43:45.111201+00:00
-- url     : https://prove2.me/theorems/caeefdff-99ab-4af5-8a0d-b785b71ecfb2
-- title:
--   Diagonal Hlawka coordinate box on [403/64, 101/16]
-- statement:
--   Let $p\in[403/64,101/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=243353/100000$, $A=37623/25000$, and $d=83989/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17253/100000)M_i$ for $h\ne i$. Then
--   $$-69933/100000\le X_{ii}\le-60037/100000,\qquad 41817/50000\le X_{ji}\le 23437/25000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w019_box (p : ℝ) (hpa : (403/64 : ℝ) ≤ p) (hpb : p ≤ (101/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (243353/100000 : ℝ) (37623/25000 : ℝ) (83989/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17253/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69933/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(60037/100000 : ℝ) else (41817/50000 : ℝ) ≤ X j i ∧ X j i ≤ (23437/25000 : ℝ) := by sorry
