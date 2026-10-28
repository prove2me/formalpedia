-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1015_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1015_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:04:56.716357+00:00
-- url     : https://prove2.me/theorems/1717026e-4ee1-4667-bae1-1a9fb6d36a2f
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[8207/2048,513/128]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73500961/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(559/5000)M_i$ and $(1397/10000)M_i$. Then $-62223/100000\le X_{ii}\le-59203/100000$ and $7941/10000\le X_{ji}\le16567/20000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1015_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8207/2048 : ℝ) ≤ p) (hpb : p ≤ (513/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73500961/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1397/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59203/100000 : ℝ) else (7941/10000 : ℝ) ≤ X j i ∧ X j i ≤ (16567/20000 : ℝ) := by sorry
