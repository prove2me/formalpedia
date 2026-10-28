-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1253_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1253_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:18:04.765366+00:00
-- url     : https://prove2.me/theorems/1a052b13-1031-4226-8dd9-6be264422ed2
-- title:
--   Hlawka rectangular localization block 3 on [8445/2048,4223/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1253_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29693/50000 : ℝ) else (80141/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8337/10000 : ℝ) := by sorry
