-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1290_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1290_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:53:22.068108+00:00
-- url     : https://prove2.me/theorems/fa576877-d16b-4e14-a2a2-81e87fcdbd72
-- title:
--   Hlawka rectangular localization block 3 on [4249/1024,2125/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1290_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by sorry
