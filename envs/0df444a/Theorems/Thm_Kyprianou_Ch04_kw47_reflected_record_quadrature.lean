-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_reflected_record_quadrature
-- name    : Kyprianou.Ch04.kw47_reflected_record_quadrature
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:18:53.520485+00:00
-- url     : https://prove2.me/theorems/2ceaacd0-f17a-4492-b352-23acaf5a9af7
-- title:
--   Reflected exponential running-record quadrature limit
-- statement:
--   The same quadrature against the running-maximum Stieltjes measure converges to the record increment. Its half-open cell masses are the record increments, and the reflected exponential equals one almost everywhere for that measure by the contact property.
-- source:
--   Kyprianou (2006), Exercise 4.7; deterministic product-grid limit.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_real_path
import Theorems.Thm_Kyprianou_Ch04_kw47_right_grid_integral_convergence
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_contact_measure
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The right-endpoint reflected exponential quadrature against
the record measure converges to the record increment. -/

theorem Kyprianou.Ch04.kw47_reflected_record_quadrature
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1) : Real) - (u n i : Real) ≤ delta n) :
    let Z : NNReal → Real := fun r =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w - runningSup L (u n i) w) *
        Z (u n (i+1))) atTop
        (nhds (runningSup L b w - runningSup L a w)) := by sorry
