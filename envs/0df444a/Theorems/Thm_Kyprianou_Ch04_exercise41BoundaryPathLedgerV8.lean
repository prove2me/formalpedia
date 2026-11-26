-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BoundaryPathLedgerV8
-- name    : Kyprianou.Ch04.exercise41BoundaryPathLedgerV8
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:22:27.541798+00:00
-- url     : https://prove2.me/theorems/98b53eaa-7db2-5594-b6d2-d4a546e62483
-- title:
--   Deterministic finite boundary ledger under local zero-visit sign conditions
-- statement:
--   Deterministic finite boundary ledger under local zero-visit sign conditions
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

theorem Kyprianou.Ch04.exercise41BoundaryPathLedgerV8
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
    let μ := (pathJumpMeasure X Xleft w).restrict
        (Set.prod (Ioc (0 : ℝ) (t : ℝ)) (Iio (0 : ℝ)))
    let Ja := fun z : ℝ × ℝ => a (Xleft z.1.toNNReal w + z.2) - a (Xleft z.1.toNNReal w)
    let Jb := fun z : ℝ × ℝ => b (Xleft z.1.toNNReal w + z.2) - b (Xleft z.1.toNNReal w)
    let A : ℝ := ∑ s ∈ (hVisits t).toFinset, if Xleft s w = 0 then 1 else 0
    let B : ℝ := (if 0 < t then 1 else 0) +
      ∑ s ∈ (hVisits t).toFinset, if s < t then 1 else 0
    Integrable Ja μ ∧ Integrable Jb μ ∧
    a (X t w) = a (X 0 w) + (∫ z, Ja z ∂μ) + A ∧
    b (X t w) = b (X 0 w) + (∫ z, Jb z ∂μ) + B := by
  sorry
