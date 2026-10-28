-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1006_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1006_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:48:41.310687+00:00
-- url     : https://prove2.me/theorems/9d5669f2-4f87-49b7-ab58-4f8455ec3411
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[4099/1024,8199/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=146827231/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11167/100000)M_i$ and $(3491/25000)M_i$. Then $-62223/100000\le X_{ii}\le-59197/100000$ and $79381/100000\le X_{ji}\le41407/50000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1006_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4099/1024 : ℝ) ≤ p) (hpb : p ≤ (8199/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146827231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3491/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59197/100000 : ℝ) else (79381/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41407/50000 : ℝ) := by sorry
