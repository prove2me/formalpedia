-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNonpositiveLatticeAEMeasurableFromDriver
-- name    : Kyprianou.Ch01.firstNonpositiveLatticeAEMeasurableFromDriver
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:01:55.842286+00:00
-- url     : https://prove2.me/theorems/ea3122ce-4c2e-4917-9682-8ac701d400ca
-- title:
--   The first nonpositive lattice passage time of a compound Poisson driver is almost-everywhere measurable
-- statement:
--   For a marked compound Poisson process with strictly positive rate, independently distributed exponential interarrival gaps and measurable jump marks, the first nonpositive time of the integer-floor compound Poisson process with any nonnegative initial integer population is an almost-everywhere measurable WithTop NNReal random variable. On the common conull event of strictly positive gaps and divergent arrival times the process is piecewise constant, so the first nonpositive level is first reached at one of the countably many measurable arrival times (or at time zero). Express this minimum by a countable selector of measurable finite-prefix lattice states and show it coincides almost surely with the exact firstNonpositiveLattice definition, including the no-hit case top. This is the stochastic stopping-time obstacle remaining after the already Proved full unstopped path and measurable stopped-operator bridges; no first offspring moment is assumed.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4, forward Lamperti no-moment path law. Required hard child of Kyprianou.Ch01.stoppedIntegerCompoundPoissonPathAEMeasurableFromDriver UUID 49405927-66dc-442e-b14c-6d9558559823, supporting original root UUID 318afc19-2086-4e20-9846-225169aaa3c1. Already Proved Kyprianou.Ch01.stoppedLatticePathMeasurableOfFirstHit UUID 800154e8-4435-4ec7-a59f-41be5dd18b3d and integerCompoundPoissonFixedTimeMeasurable UUID 4a215c58-846c-47b2-990a-fad256013ece. Requires source-faithful treatment of firstNonpositiveLattice.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNonpositiveLatticeAEMeasurableFromDriver
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ,
      AEMeasurable
        (fun ω : Ω =>
          firstNonpositiveLattice
            (integerCompoundPoisson y arrival marks) ω) Q := by
  sorry
