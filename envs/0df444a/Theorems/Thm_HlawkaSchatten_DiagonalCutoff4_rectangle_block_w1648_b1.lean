-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1648_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1648_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:20:21.233429+00:00
-- url     : https://prove2.me/theorems/e4c6681b-48b7-4d9e-a97b-f0d51f19980b
-- title:
--   Hlawka rectangular localization block 2 on [4907/1024,4911/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1648_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65059/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14651/25000 : ℝ) else (2029/2500 : ℝ) ≤ X j i ∧ X j i ≤ (22051/25000 : ℝ) := by sorry
