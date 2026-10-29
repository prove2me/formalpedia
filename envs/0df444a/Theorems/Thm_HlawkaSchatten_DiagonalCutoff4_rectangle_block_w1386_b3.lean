-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1386_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1386_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:14:49.206448+00:00
-- url     : https://prove2.me/theorems/008d8a4f-a84e-4ca0-8e03-1b5d683db91d
-- title:
--   Hlawka rectangular localization block 4 on [4345/1024,2173/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1386_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(503/800 : ℝ) ≤ X j i ∧ X j i ≤ -(59027/100000 : ℝ) else (5013/6250 : ℝ) ≤ X j i ∧ X j i ≤ (42261/50000 : ℝ) := by sorry
