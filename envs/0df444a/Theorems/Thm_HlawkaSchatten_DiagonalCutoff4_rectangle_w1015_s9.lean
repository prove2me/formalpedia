-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1015_s9
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1015_s9
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:05:27.610816+00:00
-- url     : https://prove2.me/theorems/8f3e9066-8c3b-4cf2-8dc2-6995cc7f9d4b
-- title:
--   Hlawka positive-tail refinement 10 near exponent four
-- statement:
--   Let $p\in[8207/2048,513/128]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73500961/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11179/100000)M_i$ and $(1397/10000)M_i$. Then every pair tail lies between $(559/5000)M_i$ and $(1397/10000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1015_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8207/2048 : ℝ) ≤ p) (hpb : p ≤ (513/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73500961/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1397/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (559/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1397/10000 : ℝ)*pair X i i := by sorry
