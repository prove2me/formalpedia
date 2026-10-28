-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1024_s7
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1024_s7
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:15:35.991078+00:00
-- url     : https://prove2.me/theorems/1ffea7bc-858c-4dbe-8916-931e4167d4a8
-- title:
--   Hlawka positive-tail refinement 8 near exponent four
-- statement:
--   Let $p\in[1027/256,8217/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147176677/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(5589/50000)M_i$ and $(13991/100000)M_i$. Then every pair tail lies between $(1119/10000)M_i$ and $(13979/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1024_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147176677/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13979/100000 : ℝ)*pair X i i := by sorry
