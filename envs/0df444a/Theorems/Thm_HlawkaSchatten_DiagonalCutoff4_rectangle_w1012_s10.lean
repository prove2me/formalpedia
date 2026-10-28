-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1012_s10
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1012_s10
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:01:43.433045+00:00
-- url     : https://prove2.me/theorems/513a3272-20f3-4fbe-97ee-348ac3354c6a
-- title:
--   Hlawka positive-tail refinement 11 near exponent four
-- statement:
--   Let $p\in[2051/512,8205/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=29388737/20000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(447/4000)M_i$ and $(873/6250)M_i$. Then every pair tail lies between $(1397/12500)M_i$ and $(873/6250)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1012_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29388737/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (873/6250 : ℝ)*pair X i i := by sorry
