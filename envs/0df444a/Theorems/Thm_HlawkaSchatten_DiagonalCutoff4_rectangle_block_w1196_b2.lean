-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1196_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1196_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:56:49.383771+00:00
-- url     : https://prove2.me/theorems/ec322917-2be0-48de-9e11-b7282d93e7ee
-- title:
--   Hlawka rectangular localization block 3 on [2097/512,8389/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1196_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by sorry
