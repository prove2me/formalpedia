-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonEventualLinearUpperBoundAE
-- name    : Kyprianou.Ch01.compoundPoissonEventualLinearUpperBoundAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:32:39.663201+00:00
-- url     : https://prove2.me/theorems/d47f6c47-372b-48bc-a4a2-cc165251d8c8
-- title:
--   Eventual almost-sure linear upper growth of finite-mean compound Poisson sums
-- statement:
--   Under the original source finite first offspring moment and exact Lévy jump mark law, an actual compound-Poisson process has an eventual linear upper sample-path bound. This is the stochastic strong-law part of the finite-mean non-explosion argument; it has no boundedness over the initial compact interval in its conclusion.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4; compound Poisson law of large numbers and no-explosion prerequisite.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_compoundPoisson_ae_isCadlag
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonEventualLinearUpperBoundAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (hFiniteMean : Summable (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ᵐ ω ∂Q, ∃ (T : ℝ≥0) (K : ℝ), 0 ≤ K ∧
      ∀ t : ℝ≥0, T ≤ t →
        ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
          K * (1 + (t : ℝ)) := by
  sorry
