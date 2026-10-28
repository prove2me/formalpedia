-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1192_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1192_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:55:07.114512+00:00
-- url     : https://prove2.me/theorems/aaebc18b-3ee9-4d4b-b0ea-98cbb25ae95e
-- title:
--   Hlawka rectangular localization block 2 on [131/32,8385/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1192_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by sorry
