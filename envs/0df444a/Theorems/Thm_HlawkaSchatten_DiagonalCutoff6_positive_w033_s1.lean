-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w033_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w033_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:48:45.045962+00:00
-- url     : https://prove2.me/theorems/54e7074e-3965-4dc9-b633-ae580057e22f
-- title:
--   Symmetric Hlawka tail refinement 2 on [211/32, 53/8]
-- statement:
--   Let $p\in[211/32,53/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=256321/100000$, $A=74289/50000$, and $d=84651/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(6227/12500)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(21399/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w033_s1 (p : ℝ) (hpa : (211/32 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (256321/100000 : ℝ) (74289/50000 : ℝ) (84651/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6227/12500 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (21399/100000 : ℝ)*pair X i i := by sorry
