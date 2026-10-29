-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1336_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1336_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:44:56.947334+00:00
-- url     : https://prove2.me/theorems/69c8ae87-bf6f-4aa7-8f7d-c16f8ed671c1
-- title:
--   Hlawka rectangular localization block 3 on [4295/1024,537/128]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1336_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5893/10000 : ℝ) else (79919/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84329/100000 : ℝ) := by sorry
