-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedBandLeftJumpBoundFromFibreEnvelopeV1
-- name    : Kyprianou.Ch02.compensatedBandLeftJumpBoundFromFibreEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:50:07.779969+00:00
-- url     : https://prove2.me/theorems/fe5f344b-8380-4dd6-926e-090ddcf5d2a8
-- title:
--   A finite compensated band inherits its jump bound from the time fibre count and mark envelope
-- statement:
--   For a finite measure restricted to the time window and band, the bounded signed mark integral over (0,s] converges from the left to its integral over (0,t). The deterministic compensator is continuous. The resulting jump is exactly the integral of the mark over the singleton time fibre, where the mark is bounded almost everywhere by c and the measure has total mass at most one.
-- source:
--   Kyprianou (2006), Theorem 2.1. Strict jump-size bound for the compensated small-jump component; child of sourceFaithfulSmallJumpBandsCompactJumpCapV1.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.compensatedBandLeftJumpBoundFromFibreEnvelopeV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (T : ℝ≥0) (ω : Ω) (c : ℝ) (hc : 0 ≤ c)
    (hfinite : N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | e ≤ |x| ∧ |x| < 1}) < ⊤)
    (henvelope : N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0)
    (hfibre : ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ {x : ℝ | e ≤ |x| ∧ |x| < 1}) ≤ 1)
    (t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T) :
    ∃ l : ℝ,
      Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P ν N e s ω)
        (nhdsWithin t (Set.Iio t)) (nhds l) ∧
      |Kyprianou.compensatedSmallJumpBand P ν N e t ω - l| ≤ c := by sorry
