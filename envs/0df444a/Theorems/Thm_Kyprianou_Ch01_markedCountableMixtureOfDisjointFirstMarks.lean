-- Prove2me | Theorems.Thm_Kyprianou_Ch01_markedCountableMixtureOfDisjointFirstMarks
-- name    : Kyprianou.Ch01.markedCountableMixtureOfDisjointFirstMarks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:54:38.221888+00:00
-- url     : https://prove2.me/theorems/0ea0fb1e-b74c-466e-9e35-335b6263ccb0
-- title:
--   Countably many mutually exclusive mark atoms factor their common first-arrival probability
-- statement:
--   For measurable first and second raw interarrival and mark variables, let p be an arbitrary PMF and q any real per-mark factor. If each triple event {τ0≤u, τ1≤v(k), mark0=k-1} has probability P(τ0≤u)*p(k)*q(k), then the union over all k has probability P(τ0≤u)*Σ p(k)q(k). Prove by countable disjoint union indexed by distinct mark atoms, measure_iUnion, ENNReal.tsum_toReal_eq (probability measure) and tsum_mul_left. This isolates the countable measure assembly from the source driver independence proof. No moments or finite support.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.markedCountableMixtureOfDisjointFirstMarks
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (arrival marks : ℕ → Ω → ℝ)
    (h0 : Measurable (arrival 0))
    (h1 : Measurable (arrival 1))
    (hm : Measurable (marks 0))
    (u : ℝ) (v : ℕ → ℝ) (p : PMF ℕ) (q : ℕ → ℝ)
    (hAtom : ∀ k : ℕ,
      (Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k ∧
        marks 0 ω = (k : ℝ) - 1}).toReal =
      (Q {ω | arrival 0 ω ≤ u}).toReal *
        (p k).toReal * q k) :
    (Q {ω | ∃ k : ℕ,
        marks 0 ω = (k : ℝ) - 1 ∧
        arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v k}).toReal =
      (Q {ω | arrival 0 ω ≤ u}).toReal *
        (∑' k : ℕ, (p k).toReal * q k) := by
  sorry
