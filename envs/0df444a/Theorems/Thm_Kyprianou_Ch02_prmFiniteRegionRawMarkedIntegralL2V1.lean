-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionRawMarkedIntegralL2V1
-- name    : Kyprianou.Ch02.prmFiniteRegionRawMarkedIntegralL2V1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:54:34.81492+00:00
-- url     : https://prove2.me/theorems/eb083600-ee0e-49df-bdb2-b935107049a4
-- title:
--   Finite-intensity marked Poisson integral has a finite second moment
-- statement:
--   For a finite-Lévy-measure region B and a square-integrable marked jump amplitude x, the uncompensated sum of the KLS Poisson marks on a compact time window belongs to L². This follows from Poisson second moments and the marked-jump isometry. It is the remaining source-specific stochastic-integral obligation needed to deduce L² of the compensated process by subtraction of a deterministic constant.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.9 canonical L2 target 3fda7a62 and LevyStochCalc Poisson isometry

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionRawMarkedIntegralL2V1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
    ∀ t : ℝ≥0, MemLp
      (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) 2 P := by sorry
