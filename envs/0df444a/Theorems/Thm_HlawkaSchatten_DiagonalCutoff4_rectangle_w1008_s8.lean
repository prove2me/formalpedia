-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1008_s8
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1008_s8
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:57:33.086732+00:00
-- url     : https://prove2.me/theorems/5002f978-fc4f-45a5-8b9d-ec729bda8a87
-- title:
--   Hlawka positive-tail refinement 9 near exponent four
-- statement:
--   Let $p\in[1025/256,8201/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73433023/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(5583/50000)M_i$ and $(13969/100000)M_i$. Then every pair tail lies between $(11169/100000)M_i$ and $(6983/50000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1008_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73433023/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6983/50000 : ℝ)*pair X i i := by sorry
