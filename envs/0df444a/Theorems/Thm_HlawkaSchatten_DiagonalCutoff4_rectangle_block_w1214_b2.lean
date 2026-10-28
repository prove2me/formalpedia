-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1214_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:02:52.131997+00:00
-- url     : https://prove2.me/theorems/5530989d-1451-4180-8ca0-36e0e758e3f5
-- title:
--   Hlawka rectangular localization block 3 on [4203/1024,8407/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by sorry
