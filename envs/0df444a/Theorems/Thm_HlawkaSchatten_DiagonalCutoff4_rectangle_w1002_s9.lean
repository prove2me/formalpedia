-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1002_s9
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1002_s9
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T11:58:42.766237+00:00
-- url     : https://prove2.me/theorems/e5eb5029-1524-442f-b448-14db50a78a2b
-- title:
--   Hlawka positive-tail refinement 10 near exponent four
-- statement:
--   Let $p\in[4097/1024,8195/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=146749611/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(279/2500)M_i$ and $(6981/50000)M_i$. Then every pair tail lies between $(11161/100000)M_i$ and $(13961/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1002_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4097/1024 : ℝ) ≤ p) (hpb : p ≤ (8195/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146749611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6981/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13961/100000 : ℝ)*pair X i i := by sorry
