-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1060_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:02:46.763812+00:00
-- url     : https://prove2.me/theorems/f63ba969-cdb6-4904-b29e-860c22062e8e
-- title:
--   Hlawka rectangular localization block 4 on [2063/512,8253/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(14809/25000 : ℝ) else (79553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82939/100000 : ℝ) := by sorry
