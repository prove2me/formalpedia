-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_nonnegative_w1097
-- name    : HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1097
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:58:29.913999+00:00
-- url     : https://prove2.me/theorems/b5bc1f61-6a9a-407d-a76d-8b3d1c0991df
-- title:
--   Nonnegative sharp Hlawka deficit in a localized positive chart
-- statement:
--   In the exponent interval displayed formally, a normalized frame with the displayed lower bound for the cyclic constant, nonnegative pair tails, and pair-tail ratio at most $2/5$ has nonnegative sharp Hlawka deficit. The total cap may be any $A\le3$ and the relative main parameter any real $d$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1097 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
