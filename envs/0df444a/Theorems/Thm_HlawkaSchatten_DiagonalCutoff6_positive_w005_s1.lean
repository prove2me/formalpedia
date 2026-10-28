-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w005_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w005_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:23:33.65332+00:00
-- url     : https://prove2.me/theorems/0b9beab7-0531-4c7f-a309-3a06982bc14c
-- title:
--   Symmetric Hlawka tail refinement 2 on [389/64, 195/32]
-- statement:
--   Let $p\in[389/64,195/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=58461/25000$, $A=76041/50000$, and $d=83463/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(13689/25000)M_i$ for $h\ne i$. Then\n$$|(V_i)_h|\le(3091/12500)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w005_s1 (p : ℝ) (hpa : (389/64 : ℝ) ≤ p) (hpb : p ≤ (195/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (58461/25000 : ℝ) (76041/50000 : ℝ) (83463/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13689/25000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (3091/12500 : ℝ)*pair X i i := by sorry
