-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1384_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1384_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:13:54.730748+00:00
-- url     : https://prove2.me/theorems/7d537226-9d07-43f3-8237-ed8bcc920709
-- title:
--   Hlawka rectangular localization block 3 on [4343/1024,543/128]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1384_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59023/100000 : ℝ) else (80197/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42257/50000 : ℝ) := by sorry
