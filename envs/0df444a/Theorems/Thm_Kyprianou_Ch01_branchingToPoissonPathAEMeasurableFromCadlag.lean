-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingToPoissonPathAEMeasurableFromCadlag
-- name    : Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:34:12.846799+00:00
-- url     : https://prove2.me/theorems/a50b477a-4a36-47b8-a220-857f6c082b64
-- title:
--   Almost-everywhere measurable inverse-occupation-clock branching path from càdlàg sample paths
-- statement:
--   For a nonnegative integer-valued stochastic process whose deterministic-time coordinates are measurable and whose sample paths are càdlàg almost surely, the process transformed by the right inverse of its cumulative population occupation integral is a measurable integer-valued path, modulo a set of zero probability. Prove coordinatewise: the occupation integral is measurable from rational-step approximations on càdlàg paths; each inverse clock is a random measurable extended nonnegative time; random-time evaluation of a càdlàg process is almost-everywhere measurable by rational right approximation. Construct a common measurable representative on one conull càdlàg event and then prove path-level AEMeasurable, including extinction and infinite inverse-clock cases; coordinatewise a.e. measurability alone is insufficient for an uncountable time index. No branching Markov or offspring mean assumptions are needed.
-- source:
--   Generalised first conjunct of corrected Lamperti path-map theorem d346ccdb-3e68-4130-b078-6746f99dd872, supporting accepted original Kyprianou (2006) Ch01 §1.3.4 path-law sketch 5716bfa6-f2e3-4d53-afe7-7c2bceb5f07f. Needed because prior c79965ce requires global Measurable despite only almost-sure càdlàg hypothesis. No hypothesised extra moment condition.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (P : Measure Ω)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    AEMeasurable
      (fun ω : Ω => fun t : ℝ≥0 =>
        (branchingToPoisson Y t ω : ℤ)) P := by
  sorry
