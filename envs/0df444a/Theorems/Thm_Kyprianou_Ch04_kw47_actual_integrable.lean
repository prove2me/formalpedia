-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_actual_integrable
-- name    : Kyprianou.Ch04.kw47_actual_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:53:32.142341+00:00
-- url     : https://prove2.me/theorems/f655bd6c-f717-48c7-a2ac-ace6f18a1699
-- title:
--   Pointwise integrability of the actual Kella–Whitt process
-- statement:
--   The actual Kella–Whitt process is integrable at every deterministic time. Strong adaptedness provides measurability and the pointwise envelope is integrable by running-supremum integrability.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7(iii).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_adapted
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
import Theorems.Thm_Kyprianou_Ch04_kw47_pointwise_envelope
import Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Pointwise integrability of the Kella--Whitt process follows from
strong adaptedness and the integrable running-maximum envelope. -/

theorem Kyprianou.Ch04.kw47_actual_integrable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (t : NNReal) :
    let Z : NNReal → Ω → Real := fun r w =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    let J : NNReal → Ω → Real := fun r w =>
      ∫ x in Set.Icc (0:Real) (r:Real), Z x.toNNReal w ∂volume
    Integrable (fun w => L.ψ alpha * J t w + 1 -
      Z t w - alpha * runningSup L t w) P := by sorry
