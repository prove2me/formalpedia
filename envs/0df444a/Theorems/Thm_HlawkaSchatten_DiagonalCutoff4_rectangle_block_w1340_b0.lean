-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1340_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1340_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:46:19.937343+00:00
-- url     : https://prove2.me/theorems/030a5b4c-116f-4e9d-a946-c2d19fb17ab8
-- title:
--   Hlawka rectangular localization block 1 on [4299/1024,1075/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1340_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4919/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1007/6250 : ℝ)*pair X i i := by sorry
