-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1004_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1004_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:47:53.99249+00:00
-- url     : https://prove2.me/theorems/d8e2a742-a83b-49f6-9f90-2301d9a02b5f
-- title:
--   Hlawka positive-tail refinement 4 near exponent four
-- statement:
--   Let $p\in[2049/512,8197/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=146788419/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(2103/25000)M_i$ and $(8469/50000)M_i$. Then every pair tail lies between $(5093/50000)M_i$ and $(3749/25000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1004_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2049/512 : ℝ) ≤ p) (hpb : p ≤ (8197/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146788419/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8469/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2103/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5093/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3749/25000 : ℝ)*pair X i i := by sorry
