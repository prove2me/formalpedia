-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_threshold_grid_error_bound
-- name    : Kyprianou.Ch04.ito43_threshold_grid_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:20:41.93785+00:00
-- url     : https://prove2.me/theorems/ae600bae-1d5b-57b3-8628-4ce9881f14d4
-- title:
--   Full stopped grid threshold error is bounded by one crossing-cell charge
-- statement:
--   Use the pointwise threshold error and the fact that a monotone grid has at most one strictly crossing cell. Sum the absolute errors and bound the cardinality of the crossing filter.
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

theorem Kyprianou.Ch04.ito43_threshold_grid_error_bound (X : NNReal → ℝ) (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (b t T : NNReal) (ht : t ≤ T) (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hX : ∀ s ≤ T, |X s| ≤ R)
    (hp : ∀ k < n, b ≤ t → u k < b → b < u (k+1) → |X (min t (u (k+1)))-X b| ≤ δ) :
    let Q : NNReal → ℝ := fun r => ∑ k ∈ Finset.range n,
      (X (min r (u (k+1)))-X (min r (u k)))^2/2
    |Q t-Q (min t b) - ∑ k ∈ Finset.range n,
      (if b ≤ u k then (1:ℝ) else 0)*(X (min t (u (k+1)))-X (min t (u k)))^2/2| ≤ 2*R*δ := by sorry
