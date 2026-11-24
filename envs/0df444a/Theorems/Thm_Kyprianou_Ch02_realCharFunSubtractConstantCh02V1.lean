-- Prove2me | Theorems.Thm_Kyprianou_Ch02_realCharFunSubtractConstantCh02V1
-- name    : Kyprianou.Ch02.realCharFunSubtractConstantCh02V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:23:08.322101+00:00
-- url     : https://prove2.me/theorems/3ee35c9f-d99b-413f-bf43-eb2dfafd8d81
-- title:
--   Characteristic function under subtraction of a deterministic real constant
-- statement:
--   Characteristic function under subtraction of a deterministic real constant
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem realCharFunSubtractConstantCh02V1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℝ) (hF : AEMeasurable F P) (c ξ : ℝ) :
    charFun (P.map (fun ω => F ω - c)) ξ =
      Complex.exp (((-c * ξ : ℝ) : ℂ) * Complex.I) *
        charFun (P.map F) ξ := by sorry
end Kyprianou.Ch02
