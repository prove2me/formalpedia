-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverArrivalStrictMonoDivergesPublic
-- name    : Kyprianou.Ch01.compoundPoissonDriverArrivalStrictMonoDivergesPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:34:56.301105+00:00
-- url     : https://prove2.me/theorems/ed6e88da-af29-4b48-b6f0-5e5e74fc54c7
-- title:
--   Public arrival regularity for original LeanLevy compound-Poisson driver via LevyFoundations
-- statement:
--   Any original ProbabilityTheory.IsCompoundPoissonDriver with positive rate has strictly increasing and diverging compound Poisson arrival times almost surely. Convert the original driver to the public LevyFoundations.IsCompoundPoissonDriver, whose five struct fields carry exactly the same measurable, independence and marginal-law data. Apply the two existing public Proved theorems levy_foundations_compoundDriverArrivalStrictMono and levy_foundations_compoundDriverArrivalDiverges. Both arrival functions are identical finite prefix sums, so transfer the conclusions to ProbabilityTheory.arrival by definitional equality. This supplies the common full-measure event needed to prove local constancy and all-time right continuity of the integer lattice compound Poisson process without importing private results.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4 forward Lamperti no finite offspring mean. Public theorem imports 54be42f8-539c-4d45-ab14-b6baf2123b3c and 9a47a925-ae84-4e29-8b77-5f31e660dedb, with public definitions 6a1c6576-3eb4-42f7-b90a-b55a6775a7f2 and b87aefb0-b302-4837-a9a2-97d06a411dea. Supports Open Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE UUID 89e2d356-663a-425c-afcd-ad3841267c58, a child on the accepted original Lamperti rootward path.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonDriverArrivalStrictMonoDivergesPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (τ marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver τ marks rate jumpLaw Q) :
    (∀ᵐ ω ∂Q, StrictMono (fun n => ProbabilityTheory.arrival τ n ω)) ∧
    (∀ᵐ ω ∂Q,
      Tendsto (fun n => ProbabilityTheory.arrival τ n ω) atTop atTop) := by
  sorry
