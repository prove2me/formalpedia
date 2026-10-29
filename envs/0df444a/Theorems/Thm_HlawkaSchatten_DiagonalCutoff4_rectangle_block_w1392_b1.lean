-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1392_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1392_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:15:32.723877+00:00
-- url     : https://prove2.me/theorems/fa137be2-9f8e-4ae9-9155-e71bdec2e6e8
-- title:
--   Hlawka rectangular localization block 2 on [4351/1024,17/4]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1392_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (199/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i := by sorry
