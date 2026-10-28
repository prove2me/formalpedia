-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1248_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1248_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:15:32.436987+00:00
-- url     : https://prove2.me/theorems/04b5b9dc-170b-4d72-adda-8bde0bd95bd1
-- title:
--   Hlawka rectangular localization block 4 on [1055/256,8441/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1248_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29691/50000 : ℝ) else (80127/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83359/100000 : ℝ) := by sorry
