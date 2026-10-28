-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1024_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1024_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:14:57.980219+00:00
-- url     : https://prove2.me/theorems/42e30157-3c62-40d4-b3e5-d95df0cf563f
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[1027/256,8217/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147176677/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11193/100000)M_i$ and $(1747/12500)M_i$. Then $-62223/100000\le X_{ii}\le-5921/10000$ and $79439/100000\le X_{ji}\le10357/12500$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1024_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147176677/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1747/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5921/10000 : ℝ) else (79439/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10357/12500 : ℝ) := by sorry
