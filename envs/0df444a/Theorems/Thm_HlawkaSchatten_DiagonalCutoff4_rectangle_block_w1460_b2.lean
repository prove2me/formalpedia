-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1460_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1460_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:44:20.564129+00:00
-- url     : https://prove2.me/theorems/3b072e4a-412a-4627-87ba-7fbb9e53e67d
-- title:
--   Hlawka rectangular localization block 3 on [4419/1024,1105/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1460_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1573/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(7397/12500 : ℝ) else (40309/50000 : ℝ) ≤ X j i ∧ X j i ≤ (106/125 : ℝ) := by sorry
