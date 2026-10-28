-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1310_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1310_b2
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:29:11.212983+00:00
-- url     : https://prove2.me/theorems/37db1aee-2adc-421b-9751-724ed8c26ca9
-- title:
--   Hlawka rectangular localization block 3 on [4269/1024,2135/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1310_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15711/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58879/100000 : ℝ) else (15953/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42113/50000 : ℝ) := by sorry
