-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1022_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1022_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:13:06.205665+00:00
-- url     : https://prove2.me/theorems/7b964017-1dfc-42e5-bf85-93ac1046f1c0
-- title:
--   Hlawka positive-tail refinement 5 near exponent four
-- statement:
--   Let $p\in[4107/1024,8215/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147137837/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(1281/12500)M_i$ and $(1497/10000)M_i$. Then every pair tail lies between $(437/4000)M_i$ and $(14251/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1022_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4107/1024 : ℝ) ≤ p) (hpb : p ≤ (8215/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147137837/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1497/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1281/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (437/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14251/100000 : ℝ)*pair X i i := by sorry
