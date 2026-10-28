-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1016_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1016_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:05:29.26022+00:00
-- url     : https://prove2.me/theorems/83e83eb4-f73d-43e4-b1f8-042e6e6f8061
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[513/128,8209/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=18377667/12500000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11181/100000)M_i$ and $(1397/10000)M_i$. Then $-62223/100000\le X_{ii}\le-14801/25000$ and $79413/100000\le X_{ji}\le82837/100000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1016_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (513/128 : ℝ) ≤ p) (hpb : p ≤ (8209/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18377667/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1397/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14801/25000 : ℝ) else (79413/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82837/100000 : ℝ) := by sorry
