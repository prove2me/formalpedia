-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowDiracLawV1
-- name    : Kyprianou.Ch02.prmFiniteWindowDiracLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:00:42.797742+00:00
-- url     : https://prove2.me/theorems/bcee54e1-d7b5-40f5-a6a0-0f58769ebcee
-- title:
--   Finite-rate Poisson measure restricted to each bounded time window is almost surely a finite sum of point masses
-- statement:
--   On a common conull event for all natural horizons T, the Poisson measure restricted to (0,T] × B is a finite sum of Dirac measures with weights equal to the restricted measure of each singleton. Requires true simultaneous integer-valuedness on a countable generating family; reuse Proved Kyprianou.Ch02.integerValuedFiniteSupportV1 and PoissonRandomMeasure.integer_valued on a finite-intensity region. This is a meaningful missing atomicity step, not a postulated equality for arbitrary measures.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.8, actual arbitrary LevyStochCalc PoissonRandomMeasure finite-window decomposition, connected to Eq (2.3) via Kyprianou.Ch02.finiteRegionPoissonLocallyFiniteStepRepresentationV1 (d17f62e1-b633-4f68-826e-8975dd391109).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteWindowDiracLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) {p} • Measure.dirac p := by sorry
