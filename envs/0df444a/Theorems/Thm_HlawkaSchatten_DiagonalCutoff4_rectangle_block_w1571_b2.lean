-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1571_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1571_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:27:42.262993+00:00
-- url     : https://prove2.me/theorems/cf43808b-e93d-4acf-95e6-f9ce990ab2c8
-- title:
--   Hlawka rectangular localization block 3 on [4637/1024,4639/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1571_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6383/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58907/100000 : ℝ) else (8093/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21593/25000 : ℝ) := by sorry
