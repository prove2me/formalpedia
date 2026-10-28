-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w000_s3
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w000_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:06:56.594052+00:00
-- url     : https://prove2.me/theorems/5232d0d8-077b-4d0e-9a45-8944ee06db5f
-- title:
--   Symmetric Hlawka tail refinement 4 on [6, 385/64]
-- statement:
--   Let $p\in[6,385/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=115229/50000$, $A=152691/100000$, and $d=83267/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(8919/50000)M_i$ for $h\ne i$. Then\n$$|(V_i)_h|\le(17619/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w000_s3 (p : ℝ) (hpa : (6 : ℝ) ≤ p) (hpb : p ≤ (385/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (115229/50000 : ℝ) (152691/100000 : ℝ) (83267/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8919/50000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (17619/100000 : ℝ)*pair X i i := by sorry
