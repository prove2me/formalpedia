-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w012_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w012_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:38:34.15382+00:00
-- url     : https://prove2.me/theorems/f8bb35ad-42d0-4684-9cac-5d3e6783d779
-- title:
--   Symmetric Hlawka tail refinement 5 on [99/16, 397/64]
-- statement:
--   Let $p\in[99/16,397/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=238593/100000$, $A=75633/50000$, and $d=8373/10000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17387/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(8693/50000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w012_s4 (p : ℝ) (hpa : (99/16 : ℝ) ≤ p) (hpb : p ≤ (397/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (238593/100000 : ℝ) (75633/50000 : ℝ) (8373/10000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17387/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (8693/50000 : ℝ)*pair X i i := by sorry
