-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w031_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w031_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:48:09.628504+00:00
-- url     : https://prove2.me/theorems/a0fb11be-392f-4c77-b3fd-615d3889a5e5
-- title:
--   Symmetric Hlawka tail refinement 2 on [209/32, 105/16]
-- statement:
--   Let $p\in[209/32,105/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=50717/20000$, $A=74481/50000$, and $d=21129/25000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(10073/20000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(4357/20000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w031_s1 (p : ℝ) (hpa : (209/32 : ℝ) ≤ p) (hpb : p ≤ (105/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (50717/20000 : ℝ) (74481/50000 : ℝ) (21129/25000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10073/20000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (4357/20000 : ℝ)*pair X i i := by sorry
