-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ContinuousPathLedgerV8
-- name    : Kyprianou.Ch04.exercise41ContinuousPathLedgerV8
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:22:19.876578+00:00
-- url     : https://prove2.me/theorems/11d17bcf-3391-508e-8f85-dc39b1548774
-- title:
--   Deterministic continuous piecewise C1 change of variables on a BV path
-- statement:
--   Deterministic continuous piecewise C1 change of variables on a BV path
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

theorem Kyprianou.Ch04.exercise41ContinuousPathLedgerV8
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
    (fLeft fRight : ℝ → ℝ)
    (hC1Left : ContDiff ℝ 1 fLeft) (hC1Right : ContDiff ℝ 1 fRight)
    (t : NNReal) :
    let g := fun x : ℝ => if x < 0 then fLeft x - fLeft 0
        else if 0 < x then fRight x - fRight 0 else 0
    let D := fun x : ℝ => if x < 0 then deriv fLeft x
        else if 0 < x then deriv fRight x else 0
    let μ := (pathJumpMeasure X Xleft w).restrict
        (Set.prod (Ioc (0 : ℝ) (t : ℝ)) (Iio (0 : ℝ)))
    let J := fun z : ℝ × ℝ => g (Xleft z.1.toNNReal w + z.2) - g (Xleft z.1.toNNReal w)
    Integrable J μ ∧
      g (X t w) = g (X 0 w) +
        c * (∫ s in Icc (0 : ℝ) (t : ℝ), D (X s.toNNReal w) ∂volume) +
        ∫ z, J z ∂μ := by
  sorry
