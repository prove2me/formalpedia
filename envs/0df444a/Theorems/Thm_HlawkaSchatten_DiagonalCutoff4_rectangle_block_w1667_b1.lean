-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1667_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1667_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:25:47.929516+00:00
-- url     : https://prove2.me/theorems/7a99b356-6ee3-4f77-94f8-7b75e359e058
-- title:
--   Hlawka rectangular localization block 2 on [4983/1024,4987/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1667_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65141/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58809/100000 : ℝ) else (163/200 : ℝ) ≤ X j i ∧ X j i ≤ (88387/100000 : ℝ) := by sorry
