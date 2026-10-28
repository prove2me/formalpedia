-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1294_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:53:57.294587+00:00
-- url     : https://prove2.me/theorems/dc0e1eee-f311-436f-9c1f-74d5aebd718c
-- title:
--   Hlawka rectangular localization block 4 on [4253/1024,2127/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58849/100000 : ℝ) else (79669/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84163/100000 : ℝ) := by sorry
