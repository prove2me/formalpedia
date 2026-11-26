-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BoundaryLedgersV7
-- name    : Kyprianou.Ch04.exercise41BoundaryLedgersV7
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:15:30.32773+00:00
-- url     : https://prove2.me/theorems/b67aa9a2-be7e-5048-9be6-1422b52911f1
-- title:
--   Arrival and departure indicator ledgers with integrable physical jump terms
-- statement:
--   Arrival and departure indicator ledgers with integrable physical jump terms
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BoundaryLedgersV7
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (Xleft : NNReal → Ω → ℝ)
    (hLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => L.X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w))) :
    ∀ᵐ w ∂P, ∀ (hVisits : ∀ t : NNReal,
      Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s w = 0}) (t : NNReal),
      let a := fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0
      let b := fun x : ℝ => if 0 < x then (1 : ℝ) else 0
      let μ := (pathJumpMeasure L.X Xleft w).restrict
        (Set.prod (Ioc (0 : ℝ) (t : ℝ)) (Iio (0 : ℝ)))
      let Ja := fun z : ℝ × ℝ => a (Xleft z.1.toNNReal w + z.2) - a (Xleft z.1.toNNReal w)
      let Jb := fun z : ℝ × ℝ => b (Xleft z.1.toNNReal w + z.2) - b (Xleft z.1.toNNReal w)
      let A : ℝ := ∑ s ∈ (hVisits t).toFinset, if Xleft s w = 0 then 1 else 0
      let B : ℝ := (if 0 < t then 1 else 0) +
        ∑ s ∈ (hVisits t).toFinset, if s < t then 1 else 0
      Integrable Ja μ ∧ Integrable Jb μ ∧
      a (L.X t w) = a (L.X 0 w) + (∫ z, Ja z ∂μ) + A ∧
      b (L.X t w) = b (L.X 0 w) + (∫ z, Jb z ∂μ) + B := by
  sorry
