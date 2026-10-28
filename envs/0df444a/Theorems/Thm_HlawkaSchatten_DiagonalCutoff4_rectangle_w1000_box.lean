-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1000_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1000_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T11:55:39.329082+00:00
-- url     : https://prove2.me/theorems/40f04418-bc96-456c-8f8d-03917b9c8823
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[4,8193/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73355403/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(5579/50000)M_i$ and $(349/2500)M_i$. Then $-62223/100000\le X_{ii}\le-7399/12500$ and $39681/50000\le X_{ji}\le207/250$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1000_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (8193/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73355403/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (349/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7399/12500 : ℝ) else (39681/50000 : ℝ) ≤ X j i ∧ X j i ≤ (207/250 : ℝ) := by sorry
