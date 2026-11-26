-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_grid_event_ledger
-- name    : Kyprianou.Ch04.kw48_grid_event_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:33:07.492057+00:00
-- url     : https://prove2.me/theorems/53f0103c-9ec0-5fb0-93ce-c47dc9548ce3
-- title:
--   Predictable complex product grid has zero conditional event integrals
-- statement:
--   Predictable complex product grid has zero conditional event integrals.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_term_event_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite deterministic predictable grid gain is integrable
and has zero integral on every event in the filtration before its start. -/

theorem Kyprianou.Ch04.kw48_grid_event_ledger {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I*(theta:Complex)*(L.X t w:Complex)) ∂P) =
      Complex.exp (-((t:Real):Complex)*Psi theta))
    (alpha beta : Real) (u : Nat → NNReal) (N : Nat) (hu : Monotone u)
    (a : NNReal) (ha : a ≤ u 0) :
    Integrable (Q L Psi alpha beta u N) P ∧
      ∀ A : Set Ω, MeasurableSet[F a] A →
        (∫ w in A, Q L Psi alpha beta u N w ∂P) = 0 := by sorry
