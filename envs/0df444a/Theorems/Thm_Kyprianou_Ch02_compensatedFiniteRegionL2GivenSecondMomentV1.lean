-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedFiniteRegionL2GivenSecondMomentV1
-- name    : Kyprianou.Ch02.compensatedFiniteRegionL2GivenSecondMomentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:01:07.885712+00:00
-- url     : https://prove2.me/theorems/3fda7a62-6b6a-40be-8c48-1099d342c798
-- title:
--   Compensated finite-region Poisson integral square-integrability
-- statement:
--   L² integrability of the compensated Poisson integral under the true second-moment hypothesis, via the Poisson isometry.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.9; source-exact logical decomposition of canonical 4ebdce06

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.compensatedFiniteRegionL2GivenSecondMomentV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
    ∀ t : ℝ≥0, MemLp
      (fun ω =>
        (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) -
        (t : ℝ) * (∫ x in B, x ∂ν)) 2 P := by sorry
