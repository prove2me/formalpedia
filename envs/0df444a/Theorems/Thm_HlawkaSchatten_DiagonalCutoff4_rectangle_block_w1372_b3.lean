-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1372_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1372_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:11:13.979126+00:00
-- url     : https://prove2.me/theorems/669a17c8-2fa9-4101-9b01-d58e0feb4402
-- title:
--   Hlawka rectangular localization block 4 on [4331/1024,1083/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1372_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15717/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59/100 : ℝ) else (2504/3125 : ℝ) ≤ X j i ∧ X j i ≤ (21117/25000 : ℝ) := by sorry
