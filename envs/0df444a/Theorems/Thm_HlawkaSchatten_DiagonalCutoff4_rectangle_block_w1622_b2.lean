-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1622_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1622_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:09:11.597952+00:00
-- url     : https://prove2.me/theorems/f2342186-324c-4d16-b7ad-660a0d66d400
-- title:
--   Hlawka rectangular localization block 3 on [4803/1024,4807/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1622_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (102/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(406/625 : ℝ) ≤ X j i ∧ X j i ≤ -(14581/25000 : ℝ) else (8067/10000 : ℝ) ≤ X j i ∧ X j i ≤ (43973/50000 : ℝ) := by sorry
