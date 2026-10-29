-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1356_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1356_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:00:07.061792+00:00
-- url     : https://prove2.me/theorems/bf21c723-81ba-46fb-862a-4ec1ab1c33ec
-- title:
--   Hlawka rectangular localization block 3 on [4315/1024,1079/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1356_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7371/12500 : ℝ) else (20009/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84407/100000 : ℝ) := by sorry
