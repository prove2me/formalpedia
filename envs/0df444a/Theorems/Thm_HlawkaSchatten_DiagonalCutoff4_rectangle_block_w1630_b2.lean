-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1630_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1630_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:10:29.861301+00:00
-- url     : https://prove2.me/theorems/f19f0f0c-e267-43ad-96ac-5467b43bcee4
-- title:
--   Hlawka rectangular localization block 3 on [4835/1024,4839/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1630_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3261/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (66/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16247/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(5841/10000 : ℝ) else (10103/12500 : ℝ) ≤ X j i ∧ X j i ≤ (88027/100000 : ℝ) := by sorry
