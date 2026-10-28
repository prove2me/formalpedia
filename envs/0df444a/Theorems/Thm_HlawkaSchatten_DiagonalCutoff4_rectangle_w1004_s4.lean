-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1004_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1004_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:47:52.575733+00:00
-- url     : https://prove2.me/theorems/4eb1546b-9160-4881-a619-beca997181d5
-- title:
--   Hlawka positive-tail refinement 5 near exponent four
-- statement:
--   Let $p\in[2049/512,8197/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=146788419/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(5093/50000)M_i$ and $(3749/25000)M_i$. Then every pair tail lies between $(2721/25000)M_i$ and $(2851/20000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1004_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2049/512 : ℝ) ≤ p) (hpb : p ≤ (8197/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146788419/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3749/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5093/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2851/20000 : ℝ)*pair X i i := by sorry
