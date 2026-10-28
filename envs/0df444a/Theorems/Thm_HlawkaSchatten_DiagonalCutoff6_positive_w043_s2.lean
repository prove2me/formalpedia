-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w043_s2
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w043_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:52:15.813001+00:00
-- url     : https://prove2.me/theorems/a66d87d3-e7c6-4812-9b8c-edf3eef446ca
-- title:
--   Symmetric Hlawka tail refinement 3 on [221/32, 111/16]
-- statement:
--   Let $p\in[221/32,111/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=135021/50000$, $A=29361/20000$, and $d=21323/25000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(2477/12500)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(1123/6250)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w043_s2 (p : ℝ) (hpa : (221/32 : ℝ) ≤ p) (hpb : p ≤ (111/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (135021/50000 : ℝ) (29361/20000 : ℝ) (21323/25000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2477/12500 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (1123/6250 : ℝ)*pair X i i := by sorry
