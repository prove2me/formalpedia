-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w058_s0
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w058_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:57:24.287286+00:00
-- url     : https://prove2.me/theorems/afae5f6a-64fb-4d0d-b2ec-333febfca2ab
-- title:
--   Symmetric Hlawka tail refinement 1 on [121/16, 61/8]
-- statement:
--   Let $p\in[121/16,61/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=299057/100000$, $A=71841/50000$, and $d=86477/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(21529/50000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w058_s0 (p : ℝ) (hpa : (121/16 : ℝ) ≤ p) (hpb : p ≤ (61/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (299057/100000 : ℝ) (71841/50000 : ℝ) (86477/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (21529/50000 : ℝ)*pair X i i := by sorry
