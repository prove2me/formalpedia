-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_predictable_martingale_increment_zero
-- name    : Kyprianou.Ch04.kw47_predictable_martingale_increment_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T18:20:12.980817+00:00
-- url     : https://prove2.me/theorems/0899243f-6078-425b-8073-df0049f81bef
-- title:
--   Predictable bounded transform of a martingale increment has zero expectation
-- statement:
--   For a real martingale E and a bounded F_s-measurable weight W, the expectation of W(E_t−E_s) vanishes for s≤t. Obtain the increment conditional expectation from the martingale property, the product integrability from boundedness, and apply the proved predictable real conditional-expectation cross-zero result. This is reusable for Kella–Whitt product-grid predictable sums, including event-localised gains.
-- source:
--   Kyprianou (2006), Exercise 4.7, product-grid approach; standard martingale-transform identity using Proved AvramDividend.Classical.avram_gb49_predictable_real_condExp_cross_zero.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb49_predictable_real_condExp_cross_zero
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_predictable_martingale_increment_zero
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (E : NNReal → Ω → Real) (hE : Martingale E F P)
    (W : Ω → Real) (s t : NNReal) (hst : s ≤ t)
    (hW : Measurable[F s] W) (C : Real)
    (hWBound : ∀ w, ‖W w‖ ≤ C) :
    (∫ w, W w * (E t w - E s w) ∂P) = 0 := by sorry
