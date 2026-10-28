-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1071_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:10:48.275991+00:00
-- url     : https://prove2.me/theorems/a7cf71a1-9115-4dc0-8bdd-49e4949fef8e
-- title:
--   Hlawka rectangular localization block 4 on [8263/2048,1033/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14811/25000 : ℝ) else (19897/25000 : ℝ) ≤ X j i ∧ X j i ≤ (20741/25000 : ℝ) := by sorry
