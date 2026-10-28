-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w009_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w009_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:34:15.076262+00:00
-- url     : https://prove2.me/theorems/6e4bd6e1-a0ea-448a-9fa5-5daa816a9420
-- title:
--   Symmetric Hlawka tail refinement 5 on [393/64, 197/32]
-- statement:
--   Let $p\in[393/64,197/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=59139/25000$, $A=151611/100000$, and $d=83617/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(3489/20000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(4361/25000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w009_s4 (p : ℝ) (hpa : (393/64 : ℝ) ≤ p) (hpb : p ≤ (197/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (59139/25000 : ℝ) (151611/100000 : ℝ) (83617/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3489/20000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (4361/25000 : ℝ)*pair X i i := by sorry
