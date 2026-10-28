-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1135_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1135_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:28:26.425777+00:00
-- url     : https://prove2.me/theorems/7a4d43c5-3607-4e31-99b6-43bd1db0a68c
-- title:
--   Hlawka rectangular localization block 4 on [8327/2048,1041/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1135_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59293/100000 : ℝ) else (79787/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83109/100000 : ℝ) := by sorry
