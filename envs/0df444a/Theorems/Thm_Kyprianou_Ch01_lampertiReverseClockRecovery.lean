-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiReverseClockRecovery
-- name    : Kyprianou.Ch01.lampertiReverseClockRecovery
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:17:35.049285+00:00
-- url     : https://prove2.me/theorems/4c9a6a9d-9048-4a0f-89bb-ddaf400174a5
-- title:
--   Equation (1.19): inverse-speed time change recovers the compound Poisson path before absorption
-- statement:
--   A precise pathwise sublemma for the reverse time-change (1.19): for càdlàg integer-valued X, before any visit to zero or negative states, the extended reciprocal occupation I_t and its inverse θ recover X_t. The zero-state absorbing convention is retained; strong Markov branching and the Poisson law remain distinct proof targets. Draft awaits remote Lean elaboration.
-- source:
--   Kyprianou (2006), Chapter 1, equation (1.19), printed p. 26.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiReverseClockRecovery
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℤ)
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun s : ℝ≥0 => X s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (X t ω)))
    (hlocalint : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ =>
          if 0 < X (Real.toNNReal s) ω then
            1 / (X (Real.toNNReal s) ω : ℝ)
          else 0)
        volume 0 (t : ℝ)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∀ s : ℝ≥0, s ≤ t → 0 < X s ω) →
        compoundPoissonToBranching X
          (Real.toNNReal
            (reciprocalOccupation X t ω).toReal) ω = X t ω := by
  sorry
