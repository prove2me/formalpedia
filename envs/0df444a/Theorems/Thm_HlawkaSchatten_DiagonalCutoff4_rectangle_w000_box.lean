-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w000_box
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w000_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T10:55:35.180382+00:00
-- url     : https://prove2.me/theorems/1038665f-4598-4d46-b33c-257661b1b4c3
-- title:
--   Hlawka positive-tail coordinate box near exponent four
-- statement:
--   Let $p\in[4,8193/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73355447/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11161/100000)M_i$ and $(13957/100000)M_i$. Then $-3111/5000\le X_{ii}\le-14799/25000$ and $39683/50000\le X_{ji}\le82797/100000$ for $j\ne i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w000_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (8193/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73355447/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3111/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(14799/25000 : ℝ) else (39683/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82797/100000 : ℝ) := by sorry
