-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p028
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:59:29.151298+00:00
-- url     : https://prove2.me/theorems/cfbb0932-95e3-4915-99d6-22cb4e74a392
-- title:
--   Hlawka distinct coordinate localization for 91/16 ≤ p ≤ 93/16
-- statement:
--   For p in [91/16,93/16], the displayed normalized parameters force positive pair coordinates after distinct-main and first-pair sign normalization, and bound all off-main pair ratios by two fifths.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) :
    (∀ X orders signs, OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by sorry
