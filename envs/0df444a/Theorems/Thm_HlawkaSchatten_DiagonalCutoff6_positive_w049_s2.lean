-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w049_s2
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w049_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:54:07.038446+00:00
-- url     : https://prove2.me/theorems/df886ba4-18ec-4a2e-8ceb-c1a932a997ee
-- title:
--   Symmetric Hlawka tail refinement 3 on [227/32, 57/8]
-- statement:
--   Let $p\in[227/32,57/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=139153/50000$, $A=145839/100000$, and $d=85651/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(9543/50000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(4429/25000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w049_s2 (p : ℝ) (hpa : (227/32 : ℝ) ≤ p) (hpb : p ≤ (57/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (139153/50000 : ℝ) (145839/100000 : ℝ) (85651/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9543/50000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (4429/25000 : ℝ)*pair X i i := by sorry
