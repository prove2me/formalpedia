-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1031_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1031_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:39:00.152851+00:00
-- url     : https://prove2.me/theorems/67f23cc3-898a-4f3b-9c9c-ab0c1a2927b8
-- title:
--   Hlawka positive-tail refinement 3 near exponent four
-- statement:
--   Let $p\in[8223/2048,257/64]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73656321/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(1003/20000)M_i$ and $(20951/100000)M_i$. Then every pair tail lies between $(8541/100000)M_i$ and $(8427/50000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1031_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73656321/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20951/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1003/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8427/50000 : ℝ)*pair X i i := by sorry
