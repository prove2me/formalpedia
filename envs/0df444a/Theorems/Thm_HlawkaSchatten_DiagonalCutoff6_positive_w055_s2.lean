-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w055_s2
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w055_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:55:45.218906+00:00
-- url     : https://prove2.me/theorems/3819b248-8ca3-46f7-9eea-922b64f917c2
-- title:
--   Symmetric Hlawka tail refinement 3 on [59/8, 119/16]
-- statement:
--   Let $p\in[59/8,119/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=145371/50000$, $A=18063/12500$, and $d=43079/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(622/3125)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(9611/50000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w055_s2 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (119/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (145371/50000 : ℝ) (18063/12500 : ℝ) (43079/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (622/3125 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (9611/50000 : ℝ)*pair X i i := by sorry
