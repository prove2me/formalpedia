-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1418_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1418_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:33:22.191775+00:00
-- url     : https://prove2.me/theorems/4f63cb56-a497-4de4-b0b7-28f38ca887db
-- title:
--   Hlawka rectangular localization block 3 on [4377/1024,2189/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1418_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62893/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59091/100000 : ℝ) else (20097/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84643/100000 : ℝ) := by sorry
