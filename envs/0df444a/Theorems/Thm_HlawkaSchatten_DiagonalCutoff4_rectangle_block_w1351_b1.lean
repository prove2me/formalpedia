-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1351_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1351_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:58:16.953605+00:00
-- url     : https://prove2.me/theorems/36f319d1-15b7-4d55-acfb-cc313fcf0a2a
-- title:
--   Hlawka rectangular localization block 2 on [2155/512,4311/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1351_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (991/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by sorry
