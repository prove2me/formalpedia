-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1517_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1517_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:05:00.20999+00:00
-- url     : https://prove2.me/theorems/94d72d93-c78f-4e70-8b7a-65adb441f09e
-- title:
--   Hlawka rectangular localization block 3 on [4529/1024,4531/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1517_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31873/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58651/100000 : ℝ) else (80373/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43017/50000 : ℝ) := by sorry
