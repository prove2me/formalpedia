-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1023_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1023_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:14:00.80152+00:00
-- url     : https://prove2.me/theorems/bb32c261-410f-4a70-a33f-63ed07ee7161
-- title:
--   Hlawka positive-tail refinement 6 near exponent four
-- statement:
--   Let $p\in[8215/2048,1027/256]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147157257/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(683/6250)M_i$ and $(14251/100000)M_i$. Then every pair tail lies between $(11127/100000)M_i$ and $(7021/50000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1023_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8215/2048 : ℝ) ≤ p) (hpb : p ≤ (1027/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147157257/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14251/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by sorry
