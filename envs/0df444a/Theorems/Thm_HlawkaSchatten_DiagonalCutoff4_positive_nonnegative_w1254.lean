-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_nonnegative_w1254
-- name    : HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1254
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:18:07.979497+00:00
-- url     : https://prove2.me/theorems/6605ea7a-76dd-43d4-a014-241d6c3904a5
-- title:
--   Nonnegative sharp Hlawka deficit in a localized positive chart
-- statement:
--   In the exponent interval displayed formally, a normalized frame with the displayed lower bound for the cyclic constant, nonnegative pair tails, and pair-tail ratio at most $2/5$ has nonnegative sharp Hlawka deficit. The total cap may be any $A\le3$ and the relative main parameter any real $d$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1254 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
