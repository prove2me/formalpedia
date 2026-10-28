-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1026_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1026_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:19:28.153758+00:00
-- url     : https://prove2.me/theorems/61df46b9-521f-48a7-a340-152ca196efdf
-- title:
--   Hlawka positive-tail refinement 6 near exponent four
-- statement:
--   Let $p\in[4109/1024,8219/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147215521/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(5467/50000)M_i$ and $(14251/100000)M_i$. Then every pair tail lies between $(2783/25000)M_i$ and $(14043/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1026_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4109/1024 : ℝ) ≤ p) (hpb : p ≤ (8219/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147215521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14251/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2783/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by sorry
