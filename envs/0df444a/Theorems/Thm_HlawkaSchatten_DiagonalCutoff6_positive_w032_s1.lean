-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w032_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w032_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:48:20.495979+00:00
-- url     : https://prove2.me/theorems/ade3fb62-b6d3-4821-9de4-342a4f90779d
-- title:
--   Symmetric Hlawka tail refinement 2 on [105/16, 211/32]
-- statement:
--   Let $p\in[105/16,211/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=254953/100000$, $A=148767/100000$, and $d=10573/12500$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(50087/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(5397/25000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w032_s1 (p : ℝ) (hpa : (105/16 : ℝ) ≤ p) (hpb : p ≤ (211/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (254953/100000 : ℝ) (148767/100000 : ℝ) (10573/12500 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (50087/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (5397/25000 : ℝ)*pair X i i := by sorry
