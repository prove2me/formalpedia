-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1008_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1008_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:56:59.170981+00:00
-- url     : https://prove2.me/theorems/127c8b3a-227c-462c-ac95-91c920ef7d40
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[1025/256,8201/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73433023/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(1117/10000)M_i$ and $(2793/20000)M_i$. Then $-62223/100000\le X_{ii}\le-29599/50000$ and $19847/25000\le X_{ji}\le82819/100000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1008_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73433023/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2793/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29599/50000 : ℝ) else (19847/25000 : ℝ) ≤ X j i ∧ X j i ≤ (82819/100000 : ℝ) := by sorry
