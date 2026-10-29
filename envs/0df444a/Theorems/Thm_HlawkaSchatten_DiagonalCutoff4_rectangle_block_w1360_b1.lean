-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1360_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:00:53.962982+00:00
-- url     : https://prove2.me/theorems/b5466062-dae5-4e83-be48-0c1b343881a8
-- title:
--   Hlawka rectangular localization block 2 on [4319/1024,135/32]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by sorry
