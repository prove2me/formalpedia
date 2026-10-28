-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w007_s0
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w007_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:31:04.386661+00:00
-- url     : https://prove2.me/theorems/a2e09a5e-528c-49a9-a07a-3bad14224b31
-- title:
--   Symmetric Hlawka tail refinement 1 on [391/64, 49/8]
-- statement:
--   Let $p\in[391/64,49/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=235199/100000$, $A=30369/20000$, and $d=4177/5000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(54413/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w007_s0 (p : ℝ) (hpa : (391/64 : ℝ) ≤ p) (hpb : p ≤ (49/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (235199/100000 : ℝ) (30369/20000 : ℝ) (4177/5000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (54413/100000 : ℝ)*pair X i i := by sorry
