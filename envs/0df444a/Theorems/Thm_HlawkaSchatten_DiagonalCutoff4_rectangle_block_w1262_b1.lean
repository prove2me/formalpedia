-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1262_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:41:24.140117+00:00
-- url     : https://prove2.me/theorems/ab08bc65-336d-475e-bd89-c0d7fe44fabe
-- title:
--   Hlawka rectangular localization block 2 on [4227/1024,8455/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i := by sorry
