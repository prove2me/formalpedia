-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w000_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w000_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T10:55:36.352487+00:00
-- url     : https://prove2.me/theorems/7d1a0e76-e60c-4f53-8b72-091db36cf986
-- title:
--   Hlawka positive-tail refinement 6 near exponent four
-- statement:
--   Let $p\in[4,8193/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=73355447/50000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(5439/50000)M_i$ and $(7127/50000)M_i$. Then every pair tail lies between $(11091/100000)M_i$ and $(1403/10000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w000_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (8193/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73355447/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5439/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11091/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by sorry
