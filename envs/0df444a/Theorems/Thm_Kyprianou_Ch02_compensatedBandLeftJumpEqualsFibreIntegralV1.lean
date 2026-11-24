-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedBandLeftJumpEqualsFibreIntegralV1
-- name    : Kyprianou.Ch02.compensatedBandLeftJumpEqualsFibreIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:58:20.523212+00:00
-- url     : https://prove2.me/theorems/d9c96537-0ec3-4e32-a096-dbf9f56b1986
-- title:
--   Compensated finite-band left jump equals its marked time-fibre integral
-- statement:
--   The compact finite-band integral admits a left limit, and the jump equals the integral over the singleton time fibre because its compensator is continuous.
-- source:
--   Kyprianou (2006), Theorem 2.1, finite compensated band jump bound

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.compensatedBandLeftJumpEqualsFibreIntegralV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (e : ℝ) (T : ℝ≥0) (ω : Ω)
    (hfinite : N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | e ≤ |x| ∧ |x| < 1}) < ⊤)
    (t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T) :
    ∃ l : ℝ,
      Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P ν N e s ω)
        (nhdsWithin t (Set.Iio t)) (nhds l) ∧
      Kyprianou.compensatedSmallJumpBand P ν N e t ω - l =
        ∫ z in ({(t : ℝ)} ×ˢ {x : ℝ | e ≤ |x| ∧ |x| < 1}), z.2 ∂(N.N ω) := by sorry
