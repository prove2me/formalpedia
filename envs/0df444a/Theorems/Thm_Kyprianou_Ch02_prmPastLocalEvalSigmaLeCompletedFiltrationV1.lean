-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmPastLocalEvalSigmaLeCompletedFiltrationV1
-- name    : Kyprianou.Ch02.prmPastLocalEvalSigmaLeCompletedFiltrationV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:42:17.012798+00:00
-- url     : https://prove2.me/theorems/13a41e36-3e2c-4077-9425-c1ae680289fb
-- title:
--   Past-window Poisson evaluations are measurable in the completed natural filtration
-- statement:
--   All evaluations of the KLS Poisson random measure on measurable subsets of a bounded past time-and-mark window are measurable in the completed Poisson natural filtration at that time. The existing filtration knows prefix-time counting variables for arbitrary measurable mark sets; differences and monotone-class closure yield all past-window Borel evaluations. The precise sigma inclusion is the remaining substantive ingredient for the finite-band compensated process to be strongly adapted.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.9, completed Poisson natural filtration and adaptedness of compensated integrals.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmPastLocalEvalSigmaLeCompletedFiltrationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    ∀ t : ℝ≥0,
      (⨆ C ∈ {C : Set (ℝ × ℝ) |
            C ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance) ≤ ℱ t
    := by sorry
