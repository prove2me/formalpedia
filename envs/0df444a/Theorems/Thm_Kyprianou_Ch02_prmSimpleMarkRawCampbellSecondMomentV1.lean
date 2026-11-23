-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkRawCampbellSecondMomentV1
-- name    : Kyprianou.Ch02.prmSimpleMarkRawCampbellSecondMomentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:20:59.603794+00:00
-- url     : https://prove2.me/theorems/b77faaa8-c9cf-4217-9416-72010d43cc46
-- title:
--   Exact Campbell second-moment formula for finite KLS Poisson simple-mark integrals
-- statement:
--   For every finite-intensity KLS time-mark window and any real-valued finite-range measurable mark g, the raw integral's second moment equals time times the mark squared-intensity integral plus the square of time times the mark intensity integral. This is the genuine Poisson random-measure Campbell/variance identity, derived from disjoint Poisson fibre counts and their joint independence.
-- source:
--   Kyprianou (2006), Chapter 2 Poisson marked-integral mean/variance and Lévy–Itô construction

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmSimpleMarkRawCampbellSecondMomentV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (g : SimpleFunc ℝ ℝ) (t : ℝ≥0) :
    (∫ ω, (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
      g z.2 ∂(N.N ω)) ^ 2 ∂P) =
      (t : ℝ) * (∫ x in B, (g x) ^ 2 ∂ν) +
        ((t : ℝ) * (∫ x in B, g x ∂ν)) ^ 2 := by sorry
