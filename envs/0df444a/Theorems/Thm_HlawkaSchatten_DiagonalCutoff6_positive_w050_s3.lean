-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w050_s3
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w050_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:54:36.664682+00:00
-- url     : https://prove2.me/theorems/125596e8-7957-4f3a-a9fc-558c2f8e4e16
-- title:
--   Symmetric Hlawka tail refinement 4 on [57/8, 229/32]
-- statement:
--   Let $p\in[57/8,229/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=55937/20000$, $A=145683/100000$, and $d=85709/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(707/4000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(17673/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w050_s3 (p : ℝ) (hpa : (57/8 : ℝ) ≤ p) (hpb : p ≤ (229/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55937/20000 : ℝ) (145683/100000 : ℝ) (85709/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (707/4000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (17673/100000 : ℝ)*pair X i i := by sorry
