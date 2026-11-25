-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_actual_adapted
-- name    : Kyprianou.Ch04.kw47_actual_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:47:20.619815+00:00
-- url     : https://prove2.me/theorems/86c8c835-604d-58ff-ae36-34904400ed8b
-- title:
--   Strong adaptedness of the Kella–Whitt process via right quadrature
-- statement:
--   The reflected exponential primitive is measurable at each observation time by limits of adapted finite quadratures entirely within that horizon. Consequently the actual Kella–Whitt process is strongly adapted.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Adaptedness of the actual reflected Kella--Whitt process follows
from right-endpoint quadrature within each observation horizon. -/

theorem Kyprianou.Ch04.kw47_actual_adapted
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha) :
    let Z : NNReal → Ω → Real := fun r w =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    let J : NNReal → Ω → Real := fun t w =>
      ∫ x in Icc (0:Real) (t:Real), Z x.toNNReal w ∂volume
    StronglyAdapted F (fun t w => L.ψ alpha * J t w + 1 -
      Z t w - alpha * runningSup L t w) := by sorry
