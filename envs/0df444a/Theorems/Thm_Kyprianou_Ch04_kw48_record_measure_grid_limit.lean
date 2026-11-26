-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_record_measure_grid_limit
-- name    : Kyprianou.Ch04.kw48_record_measure_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:45:38.724128+00:00
-- url     : https://prove2.me/theorems/e616322f-b9d6-527d-bcb3-66b42a81a15f
-- title:
--   Complex record-measure endpoint quadrature with physical record increments
-- statement:
--   Complex record-measure endpoint quadrature with physical record increments.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_kw48_complex_quadrature
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Convert record-measure quadrature weights to actual record increments. -/

theorem Kyprianou.Ch04.kw48_record_measure_grid_limit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (w : Ω) (a b : NNReal)
    (f : Real → Complex) (B : Real)
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n)
    (right : Bool)
    (hCont : ∀ᵐ x ∂((dividendMeasure (runningSup L) w).restrict
      (Ioc (a:Real) (b:Real))),
      ContinuousWithinAt f (if right then Ici x else Iic x) x) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
        f (if right then (u n (i+1):Real) else (u n i:Real))) atTop
      (nhds (∫ x in Ioc (a:Real) (b:Real), f x
        ∂(dividendMeasure (runningSup L) w))) := by sorry
