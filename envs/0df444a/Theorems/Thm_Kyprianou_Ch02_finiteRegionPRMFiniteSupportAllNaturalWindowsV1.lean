-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMFiniteSupportAllNaturalWindowsV1
-- name    : Kyprianou.Ch02.finiteRegionPRMFiniteSupportAllNaturalWindowsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:24:41.05459+00:00
-- url     : https://prove2.me/theorems/8c74bbad-92c3-468c-aaf7-4ac15620d3ee
-- title:
--   Lemma 2.8 finite atom support on all natural time windows
-- statement:
--   On one common full-probability event, the Poisson random measure in (0,T]×B is carried by a finite set of time–mark atoms for every natural T. Combines the Proved KLS integer-valued restricted-measure theorem with Mathlib finite atomicity, countable-a.e. intersection and the exact finite time-space reference-intensity computation. The crucial common event supports cadlag gluing.
-- source:
--   Source-faithful KLS Poisson/Atomic.lean ae_exists_finset_support; Kyprianou (2006) Lemma 2.8, cadlag finite-activity proof.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPRMFiniteSupportAllNaturalWindowsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0 := by sorry
end Kyprianou.Ch02
