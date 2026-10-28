-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w026_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w026_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:46:42.503703+00:00
-- url     : https://prove2.me/theorems/d17ca208-dc06-42f1-883f-132caa0e279f
-- title:
--   Symmetric Hlawka tail refinement 2 on [205/32, 411/64]
-- statement:
--   Let $p\in[205/32,411/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=124061/50000$, $A=149757/100000$, and $d=84239/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(25703/50000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(21739/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w026_s1 (p : ℝ) (hpa : (205/32 : ℝ) ≤ p) (hpb : p ≤ (411/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (124061/50000 : ℝ) (149757/100000 : ℝ) (84239/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25703/50000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (21739/100000 : ℝ)*pair X i i := by sorry
