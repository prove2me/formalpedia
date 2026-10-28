-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_main_injective_of_cases
-- name    : HlawkaSchatten.DiagonalCutoff4.ordered_main_injective_of_cases
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:34:26.411178+00:00
-- url     : https://prove2.me/theorems/7b44479b-475a-46a2-b7ed-2062d9d6a51a
-- title:
--   Distinct main coordinates from canonical chart exclusions
-- statement:
--   For arbitrary real p, k, A and d, exclusions of all 323 repeated-main canonical charts imply that every ordered chart has distinct main coordinates.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.ordered_main_injective_of_cases (p k A d : ℝ)
    (hcases : ∀ c : Fin 323, ∀ X : Fin 3 → Fin 3 → ℝ,
      OrderedChart p k A d X (repeatedOrders c) (repeatedSigns c) → False)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool)
    (hX : OrderedChart p k A d X orders signs) :
    Function.Injective (fun i => orders i 0) := by sorry
