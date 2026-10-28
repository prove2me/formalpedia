-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1007_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1007_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:49:59.380065+00:00
-- url     : https://prove2.me/theorems/428c6b49-4ba5-4f6f-b4ae-14723a6acb7a
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[8199/2048,1025/256]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73423319/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(349/3125)M_i$ and $(2793/20000)M_i$. Then $-62223/100000\le X_{ii}\le-59197/100000$ and $9923/12500\le X_{ji}\le82817/100000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1007_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8199/2048 : ℝ) ≤ p) (hpb : p ≤ (1025/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73423319/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2793/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (349/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59197/100000 : ℝ) else (9923/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82817/100000 : ℝ) := by sorry
