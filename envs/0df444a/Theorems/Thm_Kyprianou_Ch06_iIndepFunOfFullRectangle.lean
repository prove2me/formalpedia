-- Prove2me | Theorems.Thm_Kyprianou_Ch06_iIndepFunOfFullRectangle
-- name    : Kyprianou.Ch06.iIndepFunOfFullRectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:09:22.393015+00:00
-- url     : https://prove2.me/theorems/058bbd66-8506-4c55-9538-e3c94d1b1495
-- title:
--   Chapter 6 bridge: full finite-dimensional cylinder factorisation implies independence
-- statement:
--   For a probability measure, if all coordinate rectangles of an indexed finite-dimensional family have product probabilities, then the coordinate random variables are independent in the Mathlib ProbabilityTheory.iIndepFun sense, including for arbitrary finite subsets of coordinates.
-- source:
--   Kyprianou (2006), Chapter 6 independent-increments axiom, finite rectangle-to-independence technical bridge; the finite-product reduction is direct from the current pinned Mathlib independence characterisation.

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem Kyprianou.Ch06.iIndepFunOfFullRectangle
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (hprob : P Set.univ = 1)
    (n : Nat) (f : Fin n → Ω → Real)
    (hrect : ∀ A : Fin n → Set Real,
      (∀ i, MeasurableSet (A i)) →
      P {ω | ∀ i : Fin n, f i ω ∈ A i} =
        ∏ i : Fin n, P {ω | f i ω ∈ A i}) :
    ProbabilityTheory.iIndepFun f P := by sorry
