-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1258_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:40:13.707492+00:00
-- url     : https://prove2.me/theorems/e1a48632-9049-4630-b2eb-c3f244855433
-- title:
--   Hlawka rectangular localization block 4 on [4225/1024,8451/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5749/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(5939/10000 : ℝ) else (20039/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83381/100000 : ℝ) := by sorry
