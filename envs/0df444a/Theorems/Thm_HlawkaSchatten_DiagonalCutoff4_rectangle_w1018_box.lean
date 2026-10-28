-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1018_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1018_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:07:30.915859+00:00
-- url     : https://prove2.me/theorems/c9c1b914-c0b4-4016-9249-286afe1cc44b
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[4105/1024,8211/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147060167/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(699/6250)M_i$ and $(3493/25000)M_i$. Then $-62223/100000\le X_{ii}\le-11841/20000$ and $3971/5000\le X_{ji}\le41421/50000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1018_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147060167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11841/20000 : ℝ) else (3971/5000 : ℝ) ≤ X j i ∧ X j i ≤ (41421/50000 : ℝ) := by sorry
