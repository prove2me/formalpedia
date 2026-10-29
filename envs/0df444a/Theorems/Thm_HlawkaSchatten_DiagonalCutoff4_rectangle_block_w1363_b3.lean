-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1363_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1363_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:08:16.314926+00:00
-- url     : https://prove2.me/theorems/057db478-9343-4d16-8388-ded19de16e59
-- title:
--   Hlawka rectangular localization block 4 on [2161/512,4323/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1363_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3929/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29491/50000 : ℝ) else (20019/25000 : ℝ) ≤ X j i ∧ X j i ≤ (42217/50000 : ℝ) := by sorry
