-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w037_s3
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w037_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:50:27.530827+00:00
-- url     : https://prove2.me/theorems/c7ba5e8f-b7fc-4b77-bce5-d2e87f5ec41e
-- title:
--   Symmetric Hlawka tail refinement 4 on [215/32, 27/4]
-- statement:
--   Let $p\in[215/32,27/4]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=261801/100000$, $A=147843/100000$, and $d=42457/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(2279/12500)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(18221/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w037_s3 (p : ℝ) (hpa : (215/32 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (261801/100000 : ℝ) (147843/100000 : ℝ) (42457/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2279/12500 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (18221/100000 : ℝ)*pair X i i := by sorry
