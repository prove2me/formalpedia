-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1021_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1021_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:12:27.043152+00:00
-- url     : https://prove2.me/theorems/c9aa0569-c1d1-428b-ad2e-28923ef1557a
-- title:
--   Hlawka positive-tail refinement 7 near exponent four
-- statement:
--   Let $p\in[8213/2048,4107/1024]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147118419/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(2781/25000)M_i$ and $(14041/100000)M_i$. Then every pair tail lies between $(5587/50000)M_i$ and $(13989/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1021_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8213/2048 : ℝ) ≤ p) (hpb : p ≤ (4107/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147118419/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by sorry
