-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1389_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1389_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:15:05.020851+00:00
-- url     : https://prove2.me/theorems/0083a53d-ee82-4718-a46d-e597a2e80d13
-- title:
--   Hlawka rectangular localization block 3 on [1087/256,4349/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1389_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62877/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59033/100000 : ℝ) else (3209/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84533/100000 : ℝ) := by sorry
