-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1018_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1018_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:08:00.866645+00:00
-- url     : https://prove2.me/theorems/bf872f98-951d-4168-83a8-54aac653cf2a
-- title:
--   Hlawka positive-tail refinement 4 near exponent four
-- statement:
--   Let $p\in[4105/1024,8211/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147060167/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(8479/100000)M_i$ and $(8447/50000)M_i$. Then every pair tail lies between $(2047/20000)M_i$ and $(599/4000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1018_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147060167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8447/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2047/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (599/4000 : ℝ)*pair X i i := by sorry
