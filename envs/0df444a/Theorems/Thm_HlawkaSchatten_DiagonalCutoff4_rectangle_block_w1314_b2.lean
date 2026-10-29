-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1314_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1314_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:29:30.507202+00:00
-- url     : https://prove2.me/theorems/d10eb3d5-2c69-400b-9c0b-d5e22bab98b3
-- title:
--   Hlawka rectangular localization block 3 on [4273/1024,2137/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1314_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by sorry
