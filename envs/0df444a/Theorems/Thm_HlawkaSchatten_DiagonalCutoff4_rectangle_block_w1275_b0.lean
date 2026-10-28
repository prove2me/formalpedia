-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1275_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1275_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:49:50.976681+00:00
-- url     : https://prove2.me/theorems/7f058602-b189-4b09-b86b-4720f9e34faf
-- title:
--   Hlawka rectangular localization block 1 on [2117/512,4235/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1275_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i := by sorry
