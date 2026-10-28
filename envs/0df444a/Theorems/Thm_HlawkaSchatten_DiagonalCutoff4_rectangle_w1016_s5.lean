-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1016_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1016_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:06:27.072156+00:00
-- url     : https://prove2.me/theorems/b12dff20-37f9-4d60-92ec-a15c81159603
-- title:
--   Hlawka positive-tail refinement 6 near exponent four
-- statement:
--   Let $p\in[513/128,8209/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=18377667/12500000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(341/3125)M_i$ and $(14253/100000)M_i$. Then every pair tail lies between $(2779/25000)M_i$ and $(14039/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1016_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (513/128 : ℝ) ≤ p) (hpb : p ≤ (8209/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18377667/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14253/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (341/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2779/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by sorry
