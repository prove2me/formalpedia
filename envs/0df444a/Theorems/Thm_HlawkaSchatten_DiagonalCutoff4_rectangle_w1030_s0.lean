-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1030_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1030_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:37:57.727988+00:00
-- url     : https://prove2.me/theorems/36865385-a21d-43b9-b1ff-ca010ecd340c
-- title:
--   Hlawka positive-tail refinement 1 near exponent four
-- statement:
--   Let $p\in[4111/1024,8223/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=4602913/3125000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(0)M_i$ and $(2/5)M_i$. Then every pair tail lies between $(0)M_i$ and $(113/400)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1030_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4602913/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/400 : ℝ)*pair X i i := by sorry
