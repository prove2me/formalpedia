-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1768_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1768_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:04:26.234982+00:00
-- url     : https://prove2.me/theorems/551ba772-2c6d-4811-9080-37981ae06a89
-- title:
--   Hlawka rectangular localization block 2 on [6047/1024,6063/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1768_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (577/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8659/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58987/100000 : ℝ) else (82551/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93221/100000 : ℝ) := by sorry
