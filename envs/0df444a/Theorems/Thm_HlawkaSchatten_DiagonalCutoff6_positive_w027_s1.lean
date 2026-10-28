-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w027_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w027_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:47:04.895207+00:00
-- url     : https://prove2.me/theorems/3902ca57-b5f8-48bd-991c-9e4dd8cfbae4
-- title:
--   Symmetric Hlawka tail refinement 2 on [411/64, 103/16]
-- statement:
--   Let $p\in[411/64,103/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=49761/20000$, $A=29931/20000$, and $d=42137/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(2563/5000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(21621/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w027_s1 (p : ℝ) (hpa : (411/64 : ℝ) ≤ p) (hpb : p ≤ (103/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (49761/20000 : ℝ) (29931/20000 : ℝ) (42137/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2563/5000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (21621/100000 : ℝ)*pair X i i := by sorry
