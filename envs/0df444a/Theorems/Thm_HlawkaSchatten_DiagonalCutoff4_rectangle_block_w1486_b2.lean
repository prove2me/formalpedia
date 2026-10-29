-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1486_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1486_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:50:46.949055+00:00
-- url     : https://prove2.me/theorems/4cb34eac-0d5c-45ae-a513-37cef6afd597
-- title:
--   Hlawka rectangular localization block 3 on [4467/1024,4469/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1486_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15927/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29253/50000 : ℝ) else (16007/20000 : ℝ) ≤ X j i ∧ X j i ≤ (85833/100000 : ℝ) := by sorry
