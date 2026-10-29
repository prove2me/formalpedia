-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1406_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1406_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:31:01.976513+00:00
-- url     : https://prove2.me/theorems/94d5f0fa-328b-44d5-8c31-4ecf399d5ec2
-- title:
--   Hlawka rectangular localization block 2 on [4365/1024,2183/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1406_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by sorry
