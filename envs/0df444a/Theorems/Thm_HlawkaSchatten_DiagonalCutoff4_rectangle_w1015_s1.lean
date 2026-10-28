-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1015_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1015_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:04:54.540405+00:00
-- url     : https://prove2.me/theorems/360a9154-23b1-4f36-b6cb-7797245eeaa6
-- title:
--   Hlawka positive-tail refinement 2 near exponent four
-- statement:
--   Let $p\in[8207/2048,513/128]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73500961/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(0)M_i$ and $(28309/100000)M_i$. Then every pair tail lies between $(1233/25000)M_i$ and $(10509/50000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1015_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8207/2048 : ℝ) ≤ p) (hpb : p ≤ (513/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73500961/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28309/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1233/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10509/50000 : ℝ)*pair X i i := by sorry
