-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1350_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:58:05.496201+00:00
-- url     : https://prove2.me/theorems/0b0a75e9-5a00-45c6-a95a-6f75c6f191b8
-- title:
--   Hlawka rectangular localization block 2 on [4309/1024,2155/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (619/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by sorry
