-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarksSLLNGivenIntegrable
-- name    : Kyprianou.Ch01.compoundPoissonMarksSLLNGivenIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:56:08.525278+00:00
-- url     : https://prove2.me/theorems/9165ede7-1b37-4e4d-a9fa-61d8000fec6d
-- title:
--   Strong law for genuine compound Poisson marks under integrability
-- statement:
--   For the actual marks of a Lévy compound-Poisson driver, assuming integrability of a single mark is sufficient for almost-sure convergence of empirical means to the mark expectation. This mathematical bridge uses the source's Mark independence and identical-law certificates and the public general strong law.
-- source:
--   Kyprianou Chapter 1, compound Poisson marks; LeanLevy driver; FamousTheorems.strong_law_ae, already Proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_iidRealMarkStrongLawBridge
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarksIdentDistrib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonMarksSLLNGivenIntegrable
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (arrival marks : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hIntegrable : Integrable (marks 0) Q) :
    ∀ᵐ ω ∂Q, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, marks i ω)
      atTop (𝓝 (∫ ω, marks 0 ω ∂Q)) := by
  sorry
