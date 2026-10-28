-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1123_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1123_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:09:11.002089+00:00
-- url     : https://prove2.me/theorems/93c077ee-f6a8-409a-b4c8-05fc997bd522
-- title:
--   Hlawka rectangular localization block 4 on [8315/2048,2079/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1123_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14821/25000 : ℝ) else (319/400 : ℝ) ≤ X j i ∧ X j i ≤ (41541/50000 : ℝ) := by sorry
