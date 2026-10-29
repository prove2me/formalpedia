-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1485_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1485_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:50:34.700739+00:00
-- url     : https://prove2.me/theorems/d885a5a7-752f-49b5-8d94-6c7be3ddb659
-- title:
--   Hlawka rectangular localization block 2 on [4465/1024,4467/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1485_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5403/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by sorry
