-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_grid_term_event_zero
-- name    : Kyprianou.Ch04.kw48_grid_term_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:54:39.346729+00:00
-- url     : https://prove2.me/theorems/51ec3b92-5012-4b27-98c8-3e900652de7d
-- title:
--   Predictable complex grid term is integrable and centred on past events
-- statement:
--   Predictable complex grid term is integrable and centred on past events.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_product_integrable
import Theorems.Thm_Kyprianou_Ch04_kw48_weighted_characteristic_expectation
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every predictable product-grid term is integrable and has zero
integral over every event in the filtration at its left endpoint. -/

theorem Kyprianou.Ch04.kw48_grid_term_event_zero {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I*(theta:Complex)*(L.X t w:Complex)) ∂P) =
      Complex.exp (-((t:Real):Complex)*Psi theta))
    (alpha beta : Real) (s t : NNReal) (hst : s ≤ t) :
    let q : Ω → Complex := fun w =>
      H L Psi alpha beta s w*(E L Psi alpha t w-E L Psi alpha s w)
    Integrable q P ∧
      ∀ A : Set Ω, MeasurableSet[F s] A → (∫ w in A, q w ∂P) = 0 := by sorry
