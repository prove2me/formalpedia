-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w042_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w042_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:51:51.809802+00:00
-- url     : https://prove2.me/theorems/d623e6ea-320d-4184-a5dd-59e53ed84279
-- title:
--   Symmetric Hlawka tail refinement 2 on [55/8, 221/32]
-- statement:
--   Let $p\in[55/8,221/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=268667/100000$, $A=146973/100000$, and $d=8523/10000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1901/4000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(1247/6250)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w042_s1 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (221/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (268667/100000 : ℝ) (146973/100000 : ℝ) (8523/10000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1901/4000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (1247/6250 : ℝ)*pair X i i := by sorry
