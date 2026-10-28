-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1027_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1027_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:20:06.353682+00:00
-- url     : https://prove2.me/theorems/4feb7f4a-403d-4951-b947-1e9a11bc4e18
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[8219/2048,2055/512]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147234943/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11197/100000)M_i$ and $(6989/50000)M_i$. Then $-62223/100000\le X_{ii}\le-14803/25000$ and $9931/12500\le X_{ji}\le82863/100000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1027_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8219/2048 : ℝ) ≤ p) (hpb : p ≤ (2055/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147234943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6989/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14803/25000 : ℝ) else (9931/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82863/100000 : ℝ) := by sorry
