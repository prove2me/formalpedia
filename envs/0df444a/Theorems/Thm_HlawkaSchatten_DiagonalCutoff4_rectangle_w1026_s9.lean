-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1026_s9
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1026_s9
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:20:08.107145+00:00
-- url     : https://prove2.me/theorems/b56a1a01-76e5-4f4b-93aa-377d06599020
-- title:
--   Hlawka positive-tail refinement 10 near exponent four
-- statement:
--   Let $p\in[4109/1024,8219/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147215521/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(2239/20000)M_i$ and $(6989/50000)M_i$. Then every pair tail lies between $(2799/25000)M_i$ and $(13977/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1026_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4109/1024 : ℝ) ≤ p) (hpb : p ≤ (8219/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147215521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6989/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13977/100000 : ℝ)*pair X i i := by sorry
