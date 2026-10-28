-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w021_s0
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w021_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:44:29.784196+00:00
-- url     : https://prove2.me/theorems/a3cb63e8-2a71-4deb-a94b-cd4089dc06c8
-- title:
--   Symmetric Hlawka tail refinement 1 on [405/64, 203/32]
-- statement:
--   Let $p\in[405/64,203/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=122357/50000$, $A=150279/100000$, and $d=84061/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(13039/25000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w021_s0 (p : ℝ) (hpa : (405/64 : ℝ) ≤ p) (hpb : p ≤ (203/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (122357/50000 : ℝ) (150279/100000 : ℝ) (84061/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (13039/25000 : ℝ)*pair X i i := by sorry
