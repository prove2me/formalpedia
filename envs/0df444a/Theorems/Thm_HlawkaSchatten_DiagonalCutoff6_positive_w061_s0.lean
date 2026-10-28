-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w061_s0
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w061_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:57:57.697488+00:00
-- url     : https://prove2.me/theorems/60bc8623-a053-44f2-ba25-da42ba19b07e
-- title:
--   Symmetric Hlawka tail refinement 1 on [31/4, 125/16]
-- statement:
--   Let $p\in[31/4,125/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=307391/100000$, $A=35727/25000$, and $d=43391/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(1312/3125)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w061_s0 (p : ℝ) (hpa : (31/4 : ℝ) ≤ p) (hpb : p ≤ (125/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (307391/100000 : ℝ) (35727/25000 : ℝ) (43391/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (1312/3125 : ℝ)*pair X i i := by sorry
