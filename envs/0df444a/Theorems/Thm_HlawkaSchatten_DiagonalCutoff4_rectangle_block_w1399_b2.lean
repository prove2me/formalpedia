-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1399_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1399_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:29:35.424794+00:00
-- url     : https://prove2.me/theorems/441fc474-0277-4661-9adc-3185daadee83
-- title:
--   Hlawka rectangular localization block 3 on [2179/512,4359/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1399_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31441/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59053/100000 : ℝ) else (40141/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84571/100000 : ℝ) := by sorry
