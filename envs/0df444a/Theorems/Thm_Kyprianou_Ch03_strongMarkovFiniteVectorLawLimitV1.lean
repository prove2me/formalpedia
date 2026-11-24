-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteVectorLawLimitV1
-- name    : Kyprianou.Ch03.strongMarkovFiniteVectorLawLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:52:41.080384+00:00
-- url     : https://prove2.me/theorems/0c23c8c2-50ab-483a-b556-d1a5074a3e38
-- title:
--   Finite-vector law under almost-sure limits
-- statement:
--   Apply dominated convergence to compactly supported continuous NNReal tests under the finite measure, using equality of the approximating vector laws and uniqueness of the limiting integral.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent 6ca4e517-a112-432a-b338-6d002fb7c8aa.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovFiniteVectorLawLimitV1
    {Omega I : Type} [MeasurableSpace Omega] [Fintype I]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (Y : ℕ → Omega → (I → Real)) (Z : Omega → (I → Real))
    (hMeas : ∀ n, Measurable (Y n)) (hZ : Measurable Z)
    (hLaw : ∀ n, Measure.map (Y n) mu = Measure.map (Y 0) mu)
    (hLimit : ∀ᵐ w ∂mu, Tendsto (fun n => Y n w) atTop (nhds (Z w))) :
    Measure.map Z mu = Measure.map (Y 0) mu := by
  sorry
