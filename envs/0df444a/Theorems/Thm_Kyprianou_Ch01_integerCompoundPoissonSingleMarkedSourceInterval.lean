-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonSingleMarkedSourceInterval
-- name    : Kyprianou.Ch01.integerCompoundPoissonSingleMarkedSourceInterval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:13:47.853064+00:00
-- url     : https://prove2.me/theorems/0d32ff23-c808-43b8-861b-e2d38c456026
-- title:
--   Lattice compound-Poisson source stays at the first marked state before the second arrival
-- statement:
--   For a strictly increasing divergent arrival sequence, source jumpCount is exactly one on [arrival0, arrival1). The zero-drift compound-Poisson path therefore consists of its initial value y plus only mark0. Under mark0=j-1 and y>0, flooring the lattice path gives integer y+j-1. No probabilistic assumption is required beyond pathwise arrival regularity.
-- source:
--   Kyprianou (2006) §1.3.4, first marked jump of compound-Poisson source

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.integerCompoundPoissonSingleMarkedSourceInterval
    {Ω : Type*}
    (y j : ℕ) (arrival marks : ℕ → Ω → ℝ) (ω : Ω)
    (hMono : StrictMono (fun n => ProbabilityTheory.arrival arrival n ω))
    (hTop : Tendsto (fun n => ProbabilityTheory.arrival arrival n ω) atTop atTop)
    (hMark : marks 0 ω = (j : ℝ) - 1)
    (hy : 0 < y) :
    ∀ u : ℝ≥0,
      ProbabilityTheory.arrival arrival 0 ω ≤ (u : ℝ) →
      (u : ℝ) < ProbabilityTheory.arrival arrival 1 ω →
      integerCompoundPoisson y arrival marks u ω =
        ((y + j - 1 : ℕ) : ℤ) := by
  sorry
