-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1415_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1415_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:32:20.003091+00:00
-- url     : https://prove2.me/theorems/7fd9e2cb-404c-4b34-8999-42f99f3c0afc
-- title:
--   Hlawka rectangular localization block 3 on [2187/512,4375/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1415_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by sorry
