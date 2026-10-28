-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_chart_main_injective_of_collision_margin
-- name    : HlawkaSchatten.DiagonalCutoff4.chart_main_injective_of_collision_margin
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:43:26.029309+00:00
-- url     : https://prove2.me/theorems/4a900862-f155-453e-bc5f-d80040460377
-- title:
--   An analytic collision margin forces distinct dominant pair coordinates
-- statement:
--   For p at least one and the displayed positive parameters, any normalized ordered chart has pairwise distinct main coordinates. The explicit scalar margin replaces the finite repeated-coordinate case analysis.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.chart_main_injective_of_collision_margin (p k A d : ℝ) (hp : 1 ≤ p)
    (hd : 0 < d) (hd1 : d ≤ 1) (hk : 0 ≤ k)
    (hslope : 0 ≤ k*(2-d)-d) (hmargin : (k*(2-d)-d)*A < 3*d*(k-1))
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs) :
    Function.Injective (fun j => orders j 0) := by sorry
