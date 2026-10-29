-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1551_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1551_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:13:27.306434+00:00
-- url     : https://prove2.me/theorems/d85e738c-84f9-44a7-b3fe-afb4a85f00ca
-- title:
--   Hlawka rectangular localization block 3 on [4597/1024,4599/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1551_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63797/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14703/25000 : ℝ) else (10091/12500 : ℝ) ≤ X j i ∧ X j i ≤ (86249/100000 : ℝ) := by sorry
