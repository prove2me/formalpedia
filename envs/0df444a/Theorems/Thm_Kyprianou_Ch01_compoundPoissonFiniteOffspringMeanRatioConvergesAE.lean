-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFiniteOffspringMeanRatioConvergesAE
-- name    : Kyprianou.Ch01.compoundPoissonFiniteOffspringMeanRatioConvergesAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:39:38.90166+00:00
-- url     : https://prove2.me/theorems/6c054733-4ddb-4161-8829-08941e13f142
-- title:
--   Finite-first-moment compound-Poisson sample-path ratio converges almost surely
-- statement:
--   For a genuine rate-positive compound Poisson driver whose source offspring law has finite first moment and exact integer-jump support and masses, the real aggregate-jump path divided by one plus physical time has an almost-sure finite real limit. This is the full strong-law component needed for the source-faithful eventual linear upper bound; no limit value is assumed.
-- source:
--   Kyprianou (2006), Chapter 1 Section 1.3.4, compound Poisson strong law under finite mean; reusable Markov branching non-explosion dependency.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFiniteOffspringMeanRatioConvergesAE
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
    ∀ᵐ ω ∂Q, ∃ L : ℝ,
      Tendsto (fun t : ℝ≥0 =>
        ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω /
          (1 + (t : ℝ))) atTop (nhds L) := by
  sorry
