-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1514_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1514_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:04:18.377985+00:00
-- url     : https://prove2.me/theorems/45f99edb-51cc-4313-9b03-d7b4dfd8a717
-- title:
--   Hlawka rectangular localization block 1 on [4523/1024,4525/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1514_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15989/100000 : ℝ)*pair X i i := by sorry
