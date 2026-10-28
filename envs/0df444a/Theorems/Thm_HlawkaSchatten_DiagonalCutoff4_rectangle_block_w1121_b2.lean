-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1121_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1121_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:08:49.488693+00:00
-- url     : https://prove2.me/theorems/2c5fcae5-62bf-435c-8b38-eb36947b371b
-- title:
--   Hlawka rectangular localization block 3 on [8313/2048,4157/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1121_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by sorry
