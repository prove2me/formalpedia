-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiSingleMarkedJumpWindowAE
-- name    : Kyprianou.Ch01.reverseLampertiSingleMarkedJumpWindowAE
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T14:02:49.887794+00:00
-- url     : https://prove2.me/theorems/013d7d8e-13c6-4393-9cd6-07335b5aa214
-- title:
--   Single marked arrival determines inverse-Lamperti population before second clock
-- statement:
--   After exactly one marked source jump, the source state is y+j-1 and the reciprocal occupation clock proceeds at rate 1/(y+j-1) until the second source arrival, provided it is positive. A second arrival later than arrival0+(y+j)*t therefore cannot change the population during physical horizon t. When y=1 and j=0 the first mark causes extinction, and the inverse-speed clock absorbs at zero. Use first two strictly increasing exponential arrivals almost surely.
-- source:
--   Kyprianou (2006) §1.3.4 single first jump and inverse Lamperti clock before next arrival

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiSingleMarkedJumpWindowAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ (y : ℕ) (t : ℝ≥0), 0 < y → ∀ᵐ ω ∂Q,
      ∀ j : ℕ,
        marks 0 ω = (j : ℝ) - 1 →
        ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (t : ℝ) →
        ¬ (ProbabilityTheory.arrival arrival 1 ω ≤
          ProbabilityTheory.arrival arrival 0 ω +
            ((y + j : ℕ) : ℝ) * (t : ℝ)) →
        (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t ω).toNat = y + j - 1 := by
  sorry
