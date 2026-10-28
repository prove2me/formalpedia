-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_nonnegative_w1163
-- name    : HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1163
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:40:49.974636+00:00
-- url     : https://prove2.me/theorems/aff1e8c1-8ddd-40a8-b900-b7a8f4bc4d71
-- title:
--   Nonnegative sharp Hlawka deficit in a localized positive chart
-- statement:
--   In the exponent interval displayed formally, a normalized frame with the displayed lower bound for the cyclic constant, nonnegative pair tails, and pair-tail ratio at most $2/5$ has nonnegative sharp Hlawka deficit. The total cap may be any $A\le3$ and the relative main parameter any real $d$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.positive_nonnegative_w1163 (p A d : ℝ) (hA : A ≤ 3)
    (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
