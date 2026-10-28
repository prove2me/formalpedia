-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1251_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1251_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:16:30.060739+00:00
-- url     : https://prove2.me/theorems/a0e3e07b-415d-4c78-a2ed-f4dd0a7c50ee
-- title:
--   Hlawka rectangular localization block 2 on [8443/2048,2111/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1251_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (81/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (298/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i := by sorry
