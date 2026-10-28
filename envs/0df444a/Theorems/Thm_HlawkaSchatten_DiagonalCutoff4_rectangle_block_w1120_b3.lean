-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1120_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:08:19.311329+00:00
-- url     : https://prove2.me/theorems/0467c8e4-f8b4-48b2-ad6e-6cb128cb645a
-- title:
--   Hlawka rectangular localization block 4 on [1039/256,8313/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29641/50000 : ℝ) else (79741/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3323/4000 : ℝ) := by sorry
