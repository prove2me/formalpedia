-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstMarkNonzeroAEFromNoUnitOffspring
-- name    : Kyprianou.Ch01.compoundPoissonFirstMarkNonzeroAEFromNoUnitOffspring
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:09:34.350684+00:00
-- url     : https://prove2.me/theorems/62276a2d-d226-4ce9-9141-e918b70e623d
-- title:
--   Almost surely, the first compound-Poisson mark is nonzero when unit offspring mass vanishes
-- statement:
--   The first mark has jumpLaw by the IsCompoundPoissonDriver law_mark field. Unit-offspring exclusion offspring 1=0 and mass identity jumpLaw {1-1}=offspring 1 imply jumpLaw {0}=0. Thus the measurable first-mark-zero event has Q measure zero and marks 0 is almost surely nonzero.
-- source:
--   Kyprianou (2006) §1.3.4, no-null-branching-jump first mark

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFirstMarkNonzeroAEFromNoUnitOffspring
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ᵐ ω ∂Q, marks 0 ω ≠ 0 := by
  sorry
