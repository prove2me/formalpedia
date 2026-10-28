-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1281_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:51:04.248896+00:00
-- url     : https://prove2.me/theorems/8af00350-81e9-4067-9141-a5e0472966c4
-- title:
--   Hlawka rectangular localization block 1 on [265/64,4241/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by sorry
