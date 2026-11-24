-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpBandJumpEqSliceV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpBandJumpEqSliceV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:49:38.405799+00:00
-- url     : https://prove2.me/theorems/0d830cd1-413f-422d-a802-80e1e59fdaef
-- title:
--   The compensated finite-band jump equals its time-slice marked integral
-- statement:
--   On a finite mark band the marked integral has a left limit obtained by excluding the terminal time. The continuous linear compensator has no jump.
-- source:
--   Kyprianou (2006), Chapter 2, strict jump cap in Lévy-Itô decomposition

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open scoped Topology

open Kyprianou Kyprianou.Ch02

theorem Kyprianou.Ch02.compensatedSmallJumpBandJumpEqSliceV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (e : ℝ) (he : 0 < e) (he1 : e < 1) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ T →
      ∃ l : ℝ,
        Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P ν N e s ω)
          (nhdsWithin t (Set.Iio t)) (nhds l) ∧
        Kyprianou.compensatedSmallJumpBand P ν N e t ω - l =
          ∫ z in ({(t : ℝ)} ×ˢ {x : ℝ | e ≤ |x| ∧ |x| < 1}), z.2 ∂(N.N ω) := by sorry
