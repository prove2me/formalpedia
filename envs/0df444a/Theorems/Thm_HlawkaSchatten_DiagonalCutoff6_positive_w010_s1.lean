-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w010_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w010_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:35:34.065989+00:00
-- url     : https://prove2.me/theorems/4ac20d91-9c5d-4a19-98a5-17e5b857bd20
-- title:
--   Symmetric Hlawka tail refinement 2 on [197/32, 395/64]
-- statement:
--   Let $p\in[197/32,395/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=47447/20000$, $A=75747/50000$, and $d=16731/20000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(53907/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(11957/50000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w010_s1 (p : ℝ) (hpa : (197/32 : ℝ) ≤ p) (hpb : p ≤ (395/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47447/20000 : ℝ) (75747/50000 : ℝ) (16731/20000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (53907/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (11957/50000 : ℝ)*pair X i i := by sorry
