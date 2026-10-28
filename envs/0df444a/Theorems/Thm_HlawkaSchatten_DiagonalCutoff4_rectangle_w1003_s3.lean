-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1003_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1003_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:01:52.362274+00:00
-- url     : https://prove2.me/theorems/8f04992d-6d37-46d7-9a9e-a3de6361f933
-- title:
--   Hlawka positive-tail refinement 4 near exponent four
-- statement:
--   Let $p\in[8195/2048,2049/512]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=29353803/20000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(8407/100000)M_i$ and $(16941/100000)M_i$. Then every pair tail lies between $(10183/100000)M_i$ and $(7499/50000)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1003_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8195/2048 : ℝ) ≤ p) (hpb : p ≤ (2049/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29353803/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16941/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8407/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10183/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7499/50000 : ℝ)*pair X i i := by sorry
