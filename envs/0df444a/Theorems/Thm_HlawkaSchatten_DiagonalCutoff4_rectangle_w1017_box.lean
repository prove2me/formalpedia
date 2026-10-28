-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1017_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1017_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:06:26.165646+00:00
-- url     : https://prove2.me/theorems/c52e5072-3a93-4294-a174-aa7af2239a6c
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[8209/2048,4105/1024]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147040751/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11183/100000)M_i$ and $(13971/100000)M_i$. Then $-62223/100000\le X_{ii}\le-11841/20000$ and $79417/100000\le X_{ji}\le2071/2500$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1017_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147040751/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11841/20000 : ℝ) else (79417/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2071/2500 : ℝ) := by sorry
