-- Prove2me | Theorems.Thm_Kyprianou_Ch04_expProductClockTerminalChar
-- name    : Kyprianou.Ch04.expProductClockTerminalChar
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T07:56:41.138359+00:00
-- url     : https://prove2.me/theorems/62854e7f-86bd-4581-bc3b-cbfa0ee287cd
-- title:
--   Terminal characteristic function on the independent exponential product clock
-- statement:
--   Use Fubini, the fixed-time characteristic exponent, nonnegative support of expMeasure, and the exponential transform. The real part of Psi is nonnegative by the characteristic-function norm bound at time one.
-- source:
--   Kyprianou (2006), Exercise 4.8(ii), Wiener–Hopf transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.expProductClockTerminalChar
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (Psi : ℝ → ℂ)
    (hPsi : ∀ (t : NNReal) (theta : ℝ),
      (∫ ω, Complex.exp (Complex.I * (theta : ℂ) * (L.X t ω : ℂ)) ∂P) =
        Complex.exp (-((t : ℝ) : ℂ) * Psi theta))
    (q : ℝ) (hq : 0 < q)
    (a : ℝ) :
    (∫ z : Ω × ℝ, Complex.exp (Complex.I * (a : ℂ) *
      (L.X z.2.toNNReal z.1 : ℂ)) ∂(P.prod (expMeasure q))) =
      (q : ℂ) / (Psi a + (q : ℂ)) := by
  sorry
