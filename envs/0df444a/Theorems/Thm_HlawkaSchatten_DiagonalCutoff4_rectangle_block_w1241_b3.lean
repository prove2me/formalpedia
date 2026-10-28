-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1241_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1241_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:13:34.041727+00:00
-- url     : https://prove2.me/theorems/c2c77258-95ea-4903-8c8a-50a2cf9564a1
-- title:
--   Hlawka rectangular localization block 4 on [8433/2048,4217/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1241_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59377/100000 : ℝ) else (40053/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83343/100000 : ℝ) := by sorry
