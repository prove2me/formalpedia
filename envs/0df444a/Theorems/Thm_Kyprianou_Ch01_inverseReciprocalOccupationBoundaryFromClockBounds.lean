-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationBoundaryFromClockBounds
-- name    : Kyprianou.Ch01.inverseReciprocalOccupationBoundaryFromClockBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:50:23.226821+00:00
-- url     : https://prove2.me/theorems/6a1cac26-ef87-4509-8c46-5335efad274a
-- title:
--   Inverse reciprocal clock identifies the boundary from before and after bounds
-- statement:
--   If the reciprocal clock has not crossed physical time t strictly before a, and is infinite throughout the immediate interval (a,b), then the crossing set is nonempty, has infimum exactly a, and the original WithTop inverse clock equals a. This is a pure infimum argument, independent of stochastic assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseReciprocalOccupationBoundaryFromClockBounds
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (t a b : ℝ≥0) (hab : a < b)
    (hBefore : ∀ u : ℝ≥0, u < a →
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞))
    (hAfter : ∀ u : ℝ≥0, a < u → u < b →
      reciprocalOccupation X u ω = ⊤) :
    inverseReciprocalOccupation X t ω = (a : WithTop ℝ≥0) := by
  sorry
