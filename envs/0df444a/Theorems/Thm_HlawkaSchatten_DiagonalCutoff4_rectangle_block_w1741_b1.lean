-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1741_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1741_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:56:28.045162+00:00
-- url     : https://prove2.me/theorems/53cc008b-e962-4299-95b3-a0764001abee
-- title:
--   Hlawka rectangular localization block 2 on [5615/1024,5631/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1741_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9077/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68749/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28831/50000 : ℝ) else (81027/100000 : ℝ) ≤ X j i ∧ X j i ≤ (92729/100000 : ℝ) := by sorry
