-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1624_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1624_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:09:19.843989+00:00
-- url     : https://prove2.me/theorems/fddc25f7-759d-4dcd-a6c4-0234beb22710
-- title:
--   Hlawka rectangular localization block 3 on [4811/1024,4815/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1624_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4079/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2631/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64967/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11669/20000 : ℝ) else (80709/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43983/50000 : ℝ) := by sorry
