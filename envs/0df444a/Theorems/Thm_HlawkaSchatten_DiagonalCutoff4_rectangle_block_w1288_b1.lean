-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1288_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1288_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:52:20.95202+00:00
-- url     : https://prove2.me/theorems/6a6ad3a6-2d9d-44de-b6c3-eff20ab12a39
-- title:
--   Hlawka rectangular localization block 2 on [4247/1024,531/128]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1288_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2751/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by sorry
