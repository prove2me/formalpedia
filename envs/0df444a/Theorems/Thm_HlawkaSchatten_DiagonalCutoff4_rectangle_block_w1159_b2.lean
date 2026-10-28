-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1159_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1159_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:38:34.342782+00:00
-- url     : https://prove2.me/theorems/8b110b3c-98bf-4f25-9906-9921ca48313a
-- title:
--   Hlawka rectangular localization block 3 on [8351/2048,261/64]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1159_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by sorry
