-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1068_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1068_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:08:01.359137+00:00
-- url     : https://prove2.me/theorems/14f13131-4436-45a1-89f9-d056d6498fb5
-- title:
--   Hlawka rectangular localization block 2 on [2065/512,8261/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1068_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by sorry
