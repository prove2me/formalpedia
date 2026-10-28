-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1105_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1105_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:01:58.059037+00:00
-- url     : https://prove2.me/theorems/15a8c5d4-e03f-4f45-946e-f114a930a501
-- title:
--   Hlawka rectangular localization block 4 on [8297/2048,4149/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1105_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8297/2048 : ℝ) ≤ p) (hpb : p ≤ (4149/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148752307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5927/10000 : ℝ) else (39847/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83041/100000 : ℝ) := by sorry
