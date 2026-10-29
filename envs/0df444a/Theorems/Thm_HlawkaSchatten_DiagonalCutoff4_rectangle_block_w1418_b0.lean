-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1418_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1418_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:33:19.829209+00:00
-- url     : https://prove2.me/theorems/0a1b5501-83dd-4d4e-a6a7-ab2bdbb37b57
-- title:
--   Hlawka rectangular localization block 1 on [4377/1024,2189/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1418_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7917/50000 : ℝ)*pair X i i := by sorry
