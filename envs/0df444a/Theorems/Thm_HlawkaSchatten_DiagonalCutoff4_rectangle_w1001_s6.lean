-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1001_s6
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1001_s6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T11:55:50.625575+00:00
-- url     : https://prove2.me/theorems/be68e7cc-0381-4406-afe6-9d7b11fc77e3
-- title:
--   Hlawka positive-tail refinement 7 near exponent four
-- statement:
--   Let $p\in[8193/2048,4097/1024]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=4585319/3125000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(1109/10000)M_i$ and $(14033/100000)M_i$. Then every pair tail lies between $(11143/100000)M_i$ and $(13977/100000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1001_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4585319/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13977/100000 : ℝ)*pair X i i := by sorry
