-- Prove2me | Theorems.Thm_Kyprianou_Ch04_integrableIffFiniteSignedParts
-- name    : Kyprianou.Ch04.integrableIffFiniteSignedParts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:41:56.959703+00:00
-- url     : https://prove2.me/theorems/763933c0-1b47-59ba-a6e0-cedc33a50ad0
-- title:
--   Integrability criterion for signed parts
-- statement:
--   A measurable real function is integrable exactly when both nonnegative signed parts have finite extended integrals.
-- source:
--   Supporting lemma for Chapter 4 Corollary 4.6

import Mathlib.MeasureTheory.Function.L1Space.Integrable
open MeasureTheory Filter
open scoped ENNReal Classical
set_option autoImplicit false

/-- Integrability is equivalent to finiteness of both signed parts. -/
theorem Kyprianou.Ch04.integrableIffFiniteSignedParts {E : Type} [MeasurableSpace E]
    (mu : Measure E) (f : E → Real) (hf : Measurable f) :
    Integrable f mu ↔
      (∫⁻ z, ENNReal.ofReal (max (f z) 0) ∂mu) < ⊤ ∧
      (∫⁻ z, ENNReal.ofReal (max (-f z) 0) ∂mu) < ⊤ := by
  sorry
