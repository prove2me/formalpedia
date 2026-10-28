-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1007_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:55:58.508204+00:00
-- url     : https://prove2.me/theorems/34f13493-5566-4f98-91d0-68264a698c1d
-- title:
--   Hlawka positive-tail refinement 3 near exponent four
-- statement:
--   Let $p\in[8199/2048,1025/256]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73423319/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(489/10000)M_i$ and $(5263/25000)M_i$. Then every pair tail lies between $(8427/100000)M_i$ and $(529/3125)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1007_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8199/2048 : ℝ) ≤ p) (hpb : p ≤ (1025/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73423319/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5263/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (489/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8427/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (529/3125 : ℝ)*pair X i i := by sorry
