-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1687_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1687_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:35:56.501787+00:00
-- url     : https://prove2.me/theorems/69aba073-b307-4733-b20b-14faf5cff6ea
-- title:
--   Hlawka rectangular localization block 3 on [5111/1024,5119/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1687_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66549/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57859/100000 : ℝ) else (40349/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90087/100000 : ℝ) := by sorry
