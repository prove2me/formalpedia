-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_threshold_single_cell_error
-- name    : Kyprianou.Ch04.ito43_threshold_single_cell_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:20:45.016288+00:00
-- url     : https://prove2.me/theorems/192f94f2-148a-45a5-9a7d-30d65947418b
-- title:
--   Threshold square error is supported on the strictly crossing cell
-- statement:
--   Split the clipped increment at the threshold. When both endpoints lie on the same side the discrepancy is zero. In the crossing case the difference of squares is controlled by the post-threshold change times the bounded path range.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set

theorem Kyprianou.Ch04.ito43_threshold_single_cell_error (X : NNReal → ℝ) (a d b t T : NNReal) (had : a ≤ d) (ht : t ≤ T)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hX : ∀ s ≤ T, |X s| ≤ R)
    (hp : b ≤ t → a < b → b < d → |X (min t d)-X b| ≤ δ) :
    |(X (min t d)-X (min t a))^2/2 -
       (X (min (min t b) d)-X (min (min t b) a))^2/2 -
       (if b ≤ a then (1:ℝ) else 0)*(X (min t d)-X (min t a))^2/2|
      ≤ if a < b ∧ b < d then 2*R*δ else 0 := by sorry
