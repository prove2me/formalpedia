-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SmoothScalarChainV9
-- name    : Kyprianou.Ch04.exercise41SmoothScalarChainV9
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:30:12.341148+00:00
-- url     : https://prove2.me/theorems/aceaac47-0b18-5b02-9861-ca211be9cd3a
-- title:
--   Specialise the proved two-coordinate smooth BV chain rule to scalar functions
-- statement:
--   Specialise the proved two-coordinate smooth BV chain rule to scalar functions
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SmoothScalarChainV9
    {Ω : Type}
    (X Xleft : NNReal → Ω → ℝ) (w : Ω) (c : ℝ)
    (hd : 0 < c) (hzero : X 0 w = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (hNeg : ∀ t : NNReal, 0 < t → X t w ≤ Xleft t w)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Ioc (0 : NNReal) t => |X s w - Xleft s w|) ∧
      X t w = X 0 w + c * (t : ℝ) +
        ∑' s : Ioc (0 : NNReal) t, (X s w - Xleft s w))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (t : NNReal) :
    g (X t w) = g (X 0 w) +
      c * (∫ s in Icc (0 : ℝ) (t : ℝ), deriv g (X s.toNNReal w) ∂volume) +
      ∑' s : Ioc (0 : NNReal) t, (g (X s w) - g (Xleft s w)) := by
  sorry
