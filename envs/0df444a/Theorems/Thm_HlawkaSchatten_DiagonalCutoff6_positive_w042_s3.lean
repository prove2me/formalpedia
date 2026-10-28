-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w042_s3
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w042_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:52:11.034439+00:00
-- url     : https://prove2.me/theorems/03bbcd21-67e3-4c43-9a91-19c45ebd0c30
-- title:
--   Symmetric Hlawka tail refinement 4 on [55/8, 221/32]
-- statement:
--   Let $p\in[55/8,221/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=268667/100000$, $A=146973/100000$, and $d=8523/10000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18011/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(3601/20000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w042_s3 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (221/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (268667/100000 : ℝ) (146973/100000 : ℝ) (8523/10000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18011/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (3601/20000 : ℝ)*pair X i i := by sorry
