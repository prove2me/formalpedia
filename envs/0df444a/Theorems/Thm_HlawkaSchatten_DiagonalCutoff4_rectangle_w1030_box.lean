-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1030_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1030_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:38:48.144125+00:00
-- url     : https://prove2.me/theorems/e23116a7-5bbf-4a08-81ff-ce65df55e45a
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[4111/1024,8223/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=4602913/3125000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11201/100000)M_i$ and $(699/5000)M_i$. Then $-62223/100000\le X_{ii}\le-29607/50000$ and $39729/50000\le X_{ji}\le8287/10000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1030_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4602913/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (699/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29607/50000 : ℝ) else (39729/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8287/10000 : ℝ) := by sorry
