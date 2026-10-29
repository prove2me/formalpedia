-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1647_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1647_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:19:48.091816+00:00
-- url     : https://prove2.me/theorems/a9b09b65-a6b6-4afb-a4bc-b535b77685c5
-- title:
--   Hlawka rectangular localization block 2 on [4903/1024,4907/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1647_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i := by sorry
