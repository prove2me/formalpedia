-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1025_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1025_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:18:25.857406+00:00
-- url     : https://prove2.me/theorems/6b92f4d4-b971-4f73-a1eb-bc9cf507f350
-- title:
--   Hlawka positive-tail refinement 2 near exponent four
-- statement:
--   Let $p\in[8217/2048,4109/1024]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147196099/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(0)M_i$ and $(2827/10000)M_i$. Then every pair tail lies between $(623/12500)M_i$ and $(20977/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1025_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8217/2048 : ℝ) ≤ p) (hpb : p ≤ (4109/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147196099/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (623/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20977/100000 : ℝ)*pair X i i := by sorry
