-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1315_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1315_b2
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:29:32.608773+00:00
-- url     : https://prove2.me/theorems/6dd884ba-aa2a-4cf6-8843-e8ca018cd7bf
-- title:
--   Hlawka rectangular localization block 3 on [2137/512,4275/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1315_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58889/100000 : ℝ) else (15959/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42123/50000 : ℝ) := by sorry
