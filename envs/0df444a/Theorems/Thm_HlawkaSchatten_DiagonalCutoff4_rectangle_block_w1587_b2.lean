-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1587_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1587_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:51:10.962982+00:00
-- url     : https://prove2.me/theorems/2b1c62ac-e30b-4efa-a6c8-e88899e81112
-- title:
--   Hlawka rectangular localization block 3 on [4669/1024,4671/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1587_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4669/1024 : ℝ) ≤ p) (hpb : p ≤ (4671/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169396193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3193/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(7373/12500 : ℝ) else (2534/3125 : ℝ) ≤ X j i ∧ X j i ≤ (8647/10000 : ℝ) := by sorry
