-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSupportFromFiniteStripsV1
-- name    : Kyprianou.Ch02.prmFiniteSupportFromFiniteStripsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:28:50.848648+00:00
-- url     : https://prove2.me/theorems/18e82d47-0378-4ce9-a809-96bd56cf6d8e
-- title:
--   Finite atomic support on every bounded Poisson time window from finite unit-strip counts
-- statement:
--   Let N be a LevyStochCalc PoissonRandomMeasure on the real time-mark space, with finite intensity mark region B, and assume the almost sure common finite natural count event on all unit strips. Then on a common full-probability event, for each natural time horizon T, there is a finite set of space-time atoms carrying all N mass in (0,T] × B. The proof must use countably generated Borel-space integer-valued restricted measures and their finite atomic representation; count finiteness alone is insufficient for arbitrary measures.
-- source:
--   Kyprianou (2006) Lemma 2.8, support-to-cadlag bridge for Kyprianou.Ch02.prmFiniteRegionCadlagWithFiniteStripsV1, already connected to Eq. (2.3), mission ed6e9edb-945b-4dc1-bb4b-3eed54f89dd0.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSupportFromFiniteStripsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hCount : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ k : ℕ,
      N.N ω (Set.Ico (n : ℝ) (n + 1) ×ˢ B) = k) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0 := by sorry
