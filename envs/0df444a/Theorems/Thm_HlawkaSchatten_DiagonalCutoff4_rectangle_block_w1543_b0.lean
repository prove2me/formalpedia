-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1543_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1543_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:12:08.726568+00:00
-- url     : https://prove2.me/theorems/e28214e5-f095-499f-abdf-465b7f5629e3
-- title:
--   Hlawka rectangular localization block 1 on [4581/1024,4583/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1543_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10657/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1589/10000 : ℝ)*pair X i i := by sorry
