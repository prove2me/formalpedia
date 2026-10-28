-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1207_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1207_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:00:28.725337+00:00
-- url     : https://prove2.me/theorems/5740ba07-9df7-4c75-b7a8-f6092fef220b
-- title:
--   Hlawka rectangular localization block 4 on [8399/2048,525/128]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1207_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2859/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(389/625 : ℝ) ≤ X j i ∧ X j i ≤ -(59349/100000 : ℝ) else (16001/20000 : ℝ) ≤ X j i ∧ X j i ≤ (83269/100000 : ℝ) := by sorry
