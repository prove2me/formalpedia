-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w020_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w020_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:44:01.695+00:00
-- url     : https://prove2.me/theorems/5334f998-e03b-4b05-b8e6-cac0bc248e5b
-- title:
--   Diagonal Hlawka coordinate box on [101/16, 405/64]
-- statement:
--   Let $p\in[101/16,405/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=244033/100000$, $A=150387/100000$, and $d=3361/4000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17237/100000)M_i$ for $h\ne i$. Then
--   $$-69957/100000\le X_{ii}\le-751/1250,\qquad 20919/25000\le X_{ji}\le 18753/20000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w020_box (p : ℝ) (hpa : (101/16 : ℝ) ≤ p) (hpb : p ≤ (405/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (244033/100000 : ℝ) (150387/100000 : ℝ) (3361/4000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17237/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69957/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(751/1250 : ℝ) else (20919/25000 : ℝ) ≤ X j i ∧ X j i ≤ (18753/20000 : ℝ) := by sorry
