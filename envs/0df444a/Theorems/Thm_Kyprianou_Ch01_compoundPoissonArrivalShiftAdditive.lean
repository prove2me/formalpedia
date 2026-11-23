-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonArrivalShiftAdditive
-- name    : Kyprianou.Ch01.compoundPoissonArrivalShiftAdditive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:04:25.665352+00:00
-- url     : https://prove2.me/theorems/3407bbd7-44cb-44c2-a176-1f36feaa9ab1
-- title:
--   Arrival time after deleting the initial exponential holding time
-- statement:
--   The (n+1)-st compound Poisson physical arrival equals the first holding time plus the n-th arrival of the tail sequence beginning at index one. Deterministic sum-range equality needed for the first-jump restart of the inverse Lamperti clock.
-- source:
--   ProbabilityTheory.arrival finite-sum definition, Kyprianou (2006) section 1.3.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonArrivalShiftAdditive
    {Ω : Type*} (arrival : ℕ → Ω → ℝ)
    (w : Ω) (n : ℕ) :
    ProbabilityTheory.arrival arrival (n + 1) w =
      arrival 0 w +
        ProbabilityTheory.arrival (fun i v => arrival (i + 1) v) n w := by
  sorry
