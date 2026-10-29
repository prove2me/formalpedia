-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1419_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1419_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:33:33.854708+00:00
-- url     : https://prove2.me/theorems/2d8e814b-4353-472e-9192-6878a4c9bf0f
-- title:
--   Hlawka rectangular localization block 3 on [2189/512,4379/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1419_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62893/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59093/100000 : ℝ) else (80393/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84647/100000 : ℝ) := by sorry
