-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1067_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1067_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:07:32.281918+00:00
-- url     : https://prove2.me/theorems/e8a9f2ed-f8eb-4c68-a716-4a4fc8ce9424
-- title:
--   Hlawka rectangular localization block 4 on [8259/2048,2065/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1067_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59241/100000 : ℝ) else (3183/4000 : ℝ) ≤ X j i ∧ X j i ≤ (16591/20000 : ℝ) := by sorry
