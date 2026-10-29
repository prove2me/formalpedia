-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1590_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1590_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:54:38.218988+00:00
-- url     : https://prove2.me/theorems/5370e3d9-20aa-4cd6-bb98-5a2e1ffc41a3
-- title:
--   Hlawka rectangular localization block 3 on [4675/1024,4679/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1590_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1287/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28989/50000 : ℝ) else (10003/12500 : ℝ) ≤ X j i ∧ X j i ≤ (87617/100000 : ℝ) := by sorry
