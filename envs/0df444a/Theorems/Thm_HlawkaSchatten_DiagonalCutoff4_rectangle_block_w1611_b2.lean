-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1611_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1611_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:04:25.89873+00:00
-- url     : https://prove2.me/theorems/2bb4fa82-1f08-4e82-81e0-64f2d2665e99
-- title:
--   Hlawka rectangular localization block 3 on [4759/1024,4763/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1611_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5221/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32461/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11641/20000 : ℝ) else (40227/50000 : ℝ) ≤ X j i ∧ X j i ≤ (17567/20000 : ℝ) := by sorry
