-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1028_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1028_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:35:58.597514+00:00
-- url     : https://prove2.me/theorems/0840672c-97d4-46f9-98bb-6b8bb736fb88
-- title:
--   Hlawka positive-tail refinement 6 near exponent four
-- statement:
--   Let $p\in[2055/512,8221/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147254367/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(10939/100000)M_i$ and $(57/400)M_i$. Then every pair tail lies between $(348/3125)M_i$ and $(3511/25000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1028_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2055/512 : ℝ) ≤ p) (hpb : p ≤ (8221/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147254367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (57/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by sorry
