-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1019_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1019_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:09:21.600859+00:00
-- url     : https://prove2.me/theorems/e7e0ee0b-f578-46c8-82f5-11aed58d8a05
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[8211/2048,2053/512]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147079583/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(5593/50000)M_i$ and $(3493/25000)M_i$. Then $-62223/100000\le X_{ii}\le-29603/50000$ and $79423/100000\le X_{ji}\le20711/25000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1019_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147079583/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29603/50000 : ℝ) else (79423/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20711/25000 : ℝ) := by sorry
