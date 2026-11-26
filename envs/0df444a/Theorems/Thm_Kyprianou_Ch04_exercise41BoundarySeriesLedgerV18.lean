-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BoundarySeriesLedgerV18
-- name    : Kyprianou.Ch04.exercise41BoundarySeriesLedgerV18
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T13:18:08.909214+00:00
-- url     : https://prove2.me/theorems/c7d7b880-e44e-4da0-94d0-95023c5b2f6b
-- title:
--   Pathwise finite-support series ledger for both zero indicators
-- statement:
--   Pathwise finite-support series ledger for both zero indicators
-- source:
--   Kyprianou (2006), Exercise 4.1(ii)

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BoundarySeriesLedgerV18
    {Ω : Type}
    (X Xleft : NNReal → Ω → ℝ) (w : Ω) (c : ℝ)
    (hd : 0 < c) (hzero : X 0 w = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (hNeg : ∀ t : NNReal, 0 < t → X t w ≤ Xleft t w)
    (hNoJump : ∀ s : NNReal, 0 < s →
      Function.leftLim (fun t => X t w) s = 0 → X s w = 0)
    (hDeparture : ∀ s : NNReal, X s w = 0 → ∃ ε : NNReal, 0 < ε ∧
      ∀ u : NNReal, 0 < u → u < ε → 0 < X (s + u) w)
    (hArrival : ∀ s : NNReal, 0 < s → X s w = 0 →
      Function.leftLim (fun t => X t w) s = 0 →
      ∃ ε : NNReal, 0 < ε ∧ ∀ u : NNReal, 0 < u →
        u < min ε s → X (s - u) w < 0)
    (hVisits : ∀ t : NNReal,
      Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ X s w = 0})
    (t : NNReal) :
    let a := fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0
    let b := fun x : ℝ => if 0 < x then (1 : ℝ) else 0
    let A : ℝ := ∑ s ∈ (hVisits t).toFinset, if Xleft s w = 0 then 1 else 0
    let B : ℝ := (if 0 < t then 1 else 0) +
      ∑ s ∈ (hVisits t).toFinset, if s < t then 1 else 0
    Summable (fun s : Ioc (0 : NNReal) t => ‖a (X s w) - a (Xleft s w)‖) ∧
    Summable (fun s : Ioc (0 : NNReal) t => ‖b (X s w) - b (Xleft s w)‖) ∧
    a (X t w) = a (X 0 w) + (∑' s : Ioc (0 : NNReal) t, (a (X s w) - a (Xleft s w))) + A ∧
    b (X t w) = b (X 0 w) + (∑' s : Ioc (0 : NNReal) t, (b (X s w) - b (Xleft s w))) + B := by
  sorry
