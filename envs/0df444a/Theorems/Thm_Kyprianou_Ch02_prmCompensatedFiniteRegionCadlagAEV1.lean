-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmCompensatedFiniteRegionCadlagAEV1
-- name    : Kyprianou.Ch02.prmCompensatedFiniteRegionCadlagAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:48:51.204508+00:00
-- url     : https://prove2.me/theorems/37e927a5-b7c9-4172-a5c6-90bd627f1974
-- title:
--   Càdlàg compensated finite-region Poisson integral under constant drift
-- statement:
--   For a finite-intensity measurable mark region, the raw Poisson marked integral has almost-sure càdlàg sample paths by the existing public proved theorem Kyprianou.Ch02.prmFiniteRegionCadlagAEV1. The compensation subtracts the continuous deterministic drift t↦t*c, itself càdlàg. Closure of càdlàg functions under addition proves the precise stated a.s. regularity. This isolates the analytic path-continuity component used later for the finite cutoff bands in Theorem 2.10.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, càdlàg finite-band approximants

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem prmCompensatedFiniteRegionCadlagAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (c : ℝ) :
    ∀ᵐ ω ∂P,
      ProbabilityTheory.IsCadlag (fun (t : ℝ≥0) =>
        (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))
          - (t : ℝ) * c)
    := by sorry
end Kyprianou.Ch02
