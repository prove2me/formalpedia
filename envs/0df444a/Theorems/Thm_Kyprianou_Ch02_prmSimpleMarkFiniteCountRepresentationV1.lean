-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkFiniteCountRepresentationV1
-- name    : Kyprianou.Ch02.prmSimpleMarkFiniteCountRepresentationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:10:28.024405+00:00
-- url     : https://prove2.me/theorems/aa97988d-e500-4b18-8d7b-0f3450c8c725
-- title:
--   Almost-sure finite indexed count representation of KLS simple-mark integrals
-- statement:
--   Represent every finite-range simple mark integral in a finite-intensity KLS Poisson window as a finite sum of actual Poisson counts on measurable finite-intensity subregions. The representation holds simultaneously for every approximation index on one full-measure event and uses natural-number indexing required by the Chapter 2 parent.
-- source:
--   Kyprianou (2006), Chapter 2; KLS Poisson finite-fibre representation

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmSimpleMarkFiniteCountRepresentationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ) :
    ∀ t : ℝ≥0,
      ∃ (F : ℕ → Finset ℕ) (C : ℕ → ℕ → Set (ℝ × ℝ))
        (a : ℕ → ℕ → ℝ),
      (∀ n i, i ∈ F n → MeasurableSet (C n i)) ∧
      (∀ n i, i ∈ F n →
        LevyStochCalc.Poisson.referenceIntensity ν (C n i) ≠ ⊤) ∧
      (∀ n i, i ∈ F n →
        C n i ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) ∧
      (∀ᵐ ω ∂P, ∀ n,
        (∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal) =
          ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
            (f n) z.2 ∂(N.N ω)) := by sorry
