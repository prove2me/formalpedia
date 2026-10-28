-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w043_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w043_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:52:13.044623+00:00
-- url     : https://prove2.me/theorems/82dede42-5b53-4b0f-97d4-c26dc3367d6d
-- title:
--   Diagonal Hlawka coordinate box on [221/32, 111/16]
-- statement:
--   Let $p\in[221/32,111/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=135021/50000$, $A=29361/20000$, and $d=21323/25000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17963/100000)M_i$ for $h\ne i$. Then
--   $$-18143/25000\le X_{ii}\le-59859/100000,\qquad 83481/100000\le X_{ji}\le 19233/20000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w043_box (p : ℝ) (hpa : (221/32 : ℝ) ≤ p) (hpb : p ≤ (111/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (135021/50000 : ℝ) (29361/20000 : ℝ) (21323/25000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17963/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(18143/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59859/100000 : ℝ) else (83481/100000 : ℝ) ≤ X j i ∧ X j i ≤ (19233/20000 : ℝ) := by sorry
