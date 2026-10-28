-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1028_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1028_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:35:59.201503+00:00
-- url     : https://prove2.me/theorems/a046d926-e823-48dd-af9d-f0d32b70e0f7
-- title:
--   Hlawka positive-tail refinement 4 near exponent four
-- statement:
--   Let $p\in[2055/512,8221/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147254367/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(8527/100000)M_i$ and $(16863/100000)M_i$. Then every pair tail lies between $(2567/25000)M_i$ and $(14961/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1028_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2055/512 : ℝ) ≤ p) (hpb : p ≤ (8221/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147254367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2567/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14961/100000 : ℝ)*pair X i i := by sorry
