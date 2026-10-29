-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1632_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1632_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:10:51.753822+00:00
-- url     : https://prove2.me/theorems/72c5c5a5-98f6-4187-b647-4c2a3b442301
-- title:
--   Hlawka rectangular localization block 3 on [4843/1024,4847/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1632_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2643/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16249/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(1826/3125 : ℝ) else (40431/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44023/50000 : ℝ) := by sorry
