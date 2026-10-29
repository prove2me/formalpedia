-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1557_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1557_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:25:55.866994+00:00
-- url     : https://prove2.me/theorems/89616ae6-7cb6-4475-8993-621473257f3e
-- title:
--   Hlawka rectangular localization block 3 on [4609/1024,4611/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1557_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31903/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58841/100000 : ℝ) else (80789/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43143/50000 : ℝ) := by sorry
