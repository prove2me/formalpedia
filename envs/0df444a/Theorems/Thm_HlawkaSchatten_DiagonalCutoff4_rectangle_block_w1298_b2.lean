-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1298_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b2
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:24:21.468863+00:00
-- url     : https://prove2.me/theorems/4de0e527-3e62-4269-a0d3-19b0a15db32c
-- title:
--   Hlawka rectangular localization block 3 on [4257/1024,2129/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by sorry
