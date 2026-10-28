-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w005_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w005_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:23:28.841981+00:00
-- url     : https://prove2.me/theorems/78f160e7-6fef-473b-9e27-f3619f67e512
-- title:
--   Symmetric Hlawka tail refinement 5 on [389/64, 195/32]
-- statement:
--   Let $p\in[389/64,195/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=58461/25000$, $A=76041/50000$, and $d=83463/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(219/1250)M_i$ for $h\ne i$. Then\n$$|(V_i)_h|\le(17519/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w005_s4 (p : ℝ) (hpa : (389/64 : ℝ) ≤ p) (hpb : p ≤ (195/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (58461/25000 : ℝ) (76041/50000 : ℝ) (83463/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (219/1250 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (17519/100000 : ℝ)*pair X i i := by sorry
