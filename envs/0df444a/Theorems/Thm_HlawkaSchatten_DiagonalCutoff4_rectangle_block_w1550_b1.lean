-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1550_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1550_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:13:20.767988+00:00
-- url     : https://prove2.me/theorems/6a0950cf-511a-4b19-a861-e8fb66a7da2f
-- title:
--   Hlawka rectangular localization block 2 on [4595/1024,4597/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1550_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3967/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5351/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by sorry
