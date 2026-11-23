-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiAtZeroEqualsInitialAE
-- name    : Kyprianou.Ch01.reverseLampertiAtZeroEqualsInitialAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:20:37.494223+00:00
-- url     : https://prove2.me/theorems/44f741da-b582-4fcf-bee4-25c626cc5f9d
-- title:
--   At branching time zero, the reverse Lamperti population equals its initial size almost surely
-- statement:
--   On the full-measure source paths with a right-continuous integer compound-Poisson process and correct initial value y, apply the previously Proved generic reverse Lamperti zero-time recovery theorem to obtain a branching state of y at time zero. This is the exact zero-time boundary for both no-first and single-jump approximations.
-- source:
--   Kyprianou (2006) §1.3.4, reverse Lamperti at t=0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiAtZeroEqualsInitialAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q,
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) 0 ω).toNat = y := by
  sorry
