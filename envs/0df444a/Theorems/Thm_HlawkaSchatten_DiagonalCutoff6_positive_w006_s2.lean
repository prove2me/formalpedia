-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w006_s2
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w006_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:28:59.742327+00:00
-- url     : https://prove2.me/theorems/b9ec1150-9361-4776-ae23-c42992a5ab04
-- title:
--   Symmetric Hlawka tail refinement 3 on [195/32, 391/64]
-- statement:
--   Let $p\in[195/32,391/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=234521/100000$, $A=75981/50000$, and $d=41751/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(307/1250)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(3531/20000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w006_s2 (p : ℝ) (hpa : (195/32 : ℝ) ≤ p) (hpb : p ≤ (391/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (234521/100000 : ℝ) (75981/50000 : ℝ) (41751/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (307/1250 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (3531/20000 : ℝ)*pair X i i := by sorry
