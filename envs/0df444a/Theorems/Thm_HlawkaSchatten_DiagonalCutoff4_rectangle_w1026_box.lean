-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1026_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1026_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:18:57.305982+00:00
-- url     : https://prove2.me/theorems/c0418c86-bd97-4f14-bd54-cec88a801181
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[4109/1024,8219/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=147215521/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(2799/25000)M_i$ and $(13977/100000)M_i$. Then $-62223/100000\le X_{ii}\le-59211/100000$ and $15889/20000\le X_{ji}\le82861/100000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1026_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4109/1024 : ℝ) ≤ p) (hpb : p ≤ (8219/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147215521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59211/100000 : ℝ) else (15889/20000 : ℝ) ≤ X j i ∧ X j i ≤ (82861/100000 : ℝ) := by sorry
