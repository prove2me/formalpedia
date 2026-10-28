-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_w1006_s7
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_w1006_s7
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:49:31.168405+00:00
-- url     : https://prove2.me/theorems/31bd3533-b84f-4a9b-87bc-9f724663fbfc
-- title:
--   Hlawka positive-tail refinement 8 near exponent four
-- statement:
--   Let $p\in[4099/1024,8199/2048]$, $A\le3$, and $d\in\mathbb R$. Let $X$ satisfy the normalized frame conditions with $k=146827231/100000000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Suppose every pair tail is nonnegative and lies between $(11151/100000)M_i$ and $(699/5000)M_i$. Then every pair tail lies between $(11163/100000)M_i$ and $(873/6250)M_i$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_w1006_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4099/1024 : ℝ) ≤ p) (hpb : p ≤ (8199/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146827231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (699/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (873/6250 : ℝ)*pair X i i := by sorry
