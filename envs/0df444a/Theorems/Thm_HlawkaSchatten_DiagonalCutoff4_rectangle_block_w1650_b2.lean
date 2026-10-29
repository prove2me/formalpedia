-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1650_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1650_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:20:40.9279+00:00
-- url     : https://prove2.me/theorems/82dde06a-54ff-470e-9c41-5a93541d9d24
-- title:
--   Hlawka rectangular localization block 3 on [4915/1024,4919/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1650_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10671/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16267/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29313/50000 : ℝ) else (81197/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88223/100000 : ℝ) := by sorry
