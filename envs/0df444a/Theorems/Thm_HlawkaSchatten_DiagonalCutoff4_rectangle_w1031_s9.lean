-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1031_s9
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1031_s9
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:39:53.159401+00:00
-- url     : https://prove2.me/theorems/d3cc47f2-6ba7-4f6d-8720-9ceef1f7d50a
-- title:
--   Hlawka positive-tail refinement 10 near exponent four
-- statement:
--   Let $p\in[8223/2048,257/64]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73656321/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(5601/50000)M_i$ and $(13981/100000)M_i$. Then every pair tail lies between $(11203/100000)M_i$ and $(699/5000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1031_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73656321/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (699/5000 : ℝ)*pair X i i := by sorry
