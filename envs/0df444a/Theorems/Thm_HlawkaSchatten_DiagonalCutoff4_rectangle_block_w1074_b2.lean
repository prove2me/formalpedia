-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1074_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:12:39.2065+00:00
-- url     : https://prove2.me/theorems/91d5bd54-fcd1-40e2-bd45-6928f510690d
-- title:
--   Hlawka rectangular localization block 3 on [4133/1024,8267/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i := by sorry
