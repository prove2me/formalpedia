-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w015_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w015_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:42:21.997998+00:00
-- url     : https://prove2.me/theorems/07d14a50-3af2-446b-8e02-e94dfd60f1da
-- title:
--   Symmetric Hlawka tail refinement 5 on [399/64, 25/4]
-- statement:
--   Let $p\in[399/64,25/4]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=30079/12500$, $A=15093/10000$, and $d=41921/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17329/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(1083/6250)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w015_s4 (p : ℝ) (hpa : (399/64 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30079/12500 : ℝ) (15093/10000 : ℝ) (41921/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17329/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (1083/6250 : ℝ)*pair X i i := by sorry
