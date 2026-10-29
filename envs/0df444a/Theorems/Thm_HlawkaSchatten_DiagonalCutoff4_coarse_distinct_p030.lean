-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p030
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:04:31.21283+00:00
-- url     : https://prove2.me/theorems/268f2788-45b7-4ae4-bcfb-c98f81c52aa2
-- title:
--   Hlawka distinct coordinate localization for 95/16 ≤ p ≤ 6
-- statement:
--   For p in [95/16,6], the displayed normalized parameters force positive pair coordinates after distinct-main and first-pair sign normalization, and bound all off-main pair ratios by two fifths.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) :
    (∀ X orders signs, OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by sorry
