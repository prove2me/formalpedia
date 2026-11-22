-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonRightContinuousAE
-- name    : Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:26:37.663739+00:00
-- url     : https://prove2.me/theorems/89e2d356-663a-425c-afcd-ad3841267c58
-- title:
--   The integer lattice compound-Poisson path is almost surely right-continuous at every time
-- statement:
--   Under the source compound-Poisson driver assumptions and strictly positive rate, each integer-floor lattice compound-Poisson path with integer initial population is right-continuous at every nonnegative time on a single full-measure event. On that event exponential interarrival gaps are positive, cumulative arrivals are strictly increasing and tend to infinity, and jumpCount is locally constant on a right-neighbourhood of each time. The compound-Poisson mark partial sum, integer floor and initial integer offset are therefore locally constant on each such interval. This proves exactly the path regularity needed to identify the source firstNonpositiveLattice with its measurable rational clock and close the original no-moment Lamperti stopped-driver measurability branch.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4; direct regularity bottleneck of Kyprianou.Ch01.firstNonpositiveLatticeAEMeasurableFromDriver ea3122ce-4c2e-4917-9682-8ac701d400ca. Existing ProbabilityTheory.compoundPoisson_ae_isCadlag private theorem 74d4b2ab-93f9-48be-8d72-8b726fd40c72 demonstrates source-fidelity but cannot be imported by this public target. Reconstruct from public driver fields and finite sums, using the strict-positive and divergent arrivals.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.integerCompoundPoissonRightContinuousAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 => integerCompoundPoisson y arrival marks s ω)
        (Set.Ici t) t := by
  sorry
