-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1019_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1019_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:09:21.169982+00:00
-- url     : https://prove2.me/theorems/080e7e79-6caa-4280-b048-ec58dc12cf38
-- title:
--   Hlawka positive-tail refinement 3 near exponent four
-- statement:
--   Let $p\in[8211/2048,2053/512]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147079583/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(4953/100000)M_i$ and $(10501/50000)M_i$. Then every pair tail lies between $(2121/25000)M_i$ and $(16891/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1019_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147079583/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10501/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4953/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2121/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16891/100000 : ℝ)*pair X i i := by sorry
