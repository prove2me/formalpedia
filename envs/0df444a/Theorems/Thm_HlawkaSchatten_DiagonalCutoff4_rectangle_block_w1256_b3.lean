-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1256_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1256_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:29:12.541275+00:00
-- url     : https://prove2.me/theorems/55a78306-b943-4f6b-8845-17c4571f0b18
-- title:
--   Hlawka rectangular localization block 4 on [33/8,8449/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1256_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59389/100000 : ℝ) else (1603/2000 : ℝ) ≤ X j i ∧ X j i ≤ (5211/6250 : ℝ) := by sorry
