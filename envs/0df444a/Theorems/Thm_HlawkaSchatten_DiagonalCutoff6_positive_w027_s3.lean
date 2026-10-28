-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w027_s3
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w027_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:47:09.823645+00:00
-- url     : https://prove2.me/theorems/5bbf0abb-c91b-4d6f-97ee-95fd6b0c1607
-- title:
--   Symmetric Hlawka tail refinement 4 on [411/64, 103/16]
-- statement:
--   Let $p\in[411/64,103/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=49761/20000$, $A=29931/20000$, and $d=42137/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17147/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(3421/20000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w027_s3 (p : ℝ) (hpa : (411/64 : ℝ) ≤ p) (hpb : p ≤ (103/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (49761/20000 : ℝ) (29931/20000 : ℝ) (42137/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17147/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (3421/20000 : ℝ)*pair X i i := by sorry
