-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonCompactUpperBoundAE
-- name    : Kyprianou.Ch01.compoundPoissonCompactUpperBoundAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:29:45.319693+00:00
-- url     : https://prove2.me/theorems/dbf2fd17-3bae-4c47-b07d-0ee3ba2124f0
-- title:
--   Almost-sure compact-horizon upper boundedness of compound-Poisson paths
-- statement:
--   Every càdlàg compound-Poisson path is bounded on each compact time interval almost surely; the finite-horizon bound is allowed to depend on the sample path and horizon. Reuses the Proved compoundPoisson_ae_isCadlag and cadlag_runningSup_bddAbove theorems.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4; sample path boundedness consequence of càdlàg regularity.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_compoundPoisson_ae_isCadlag
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonCompactUpperBoundAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ᵐ ω ∂Q,
      ∀ T : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧
        ∀ t : ℝ≥0, t ≤ T →
          ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤ K := by
  sorry
